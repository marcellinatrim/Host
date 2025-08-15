// Pavuk2.go — Crowd UGC Crawler (v2, HTML-forms only)
// ОС: Windows, ЯП: Go. Максимально агрессивный, без robots/sitemap, без JS.
// Находит: comments, forum, article-submit, guestbook, review, blog.
// Фильтрует: contact/обратная связь, поиск, подписка, e-commerce, чистые логины.
// Глубина: ≤3. На домен: до 500 находок (если меньше — не останавливается, пока не кончатся страницы).

package main

// ====================== Imports ======================
import (
	"bufio"
	"bytes"
	"context"
	"crypto/tls"
	"encoding/json"
	"flag"
	"fmt"
	"hash/fnv"
	"io"
	"log"
	"math"
	"math/rand"
	"net/http"
	"net/url"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/PuerkitoBio/goquery"
	"golang.org/x/time/rate"
)

var defaultUserAgents = []string{
	"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
	"Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:121.0) Gecko/20100101 Firefox/121.0",
	"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36 Edg/119.0.0.0",
	"Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
	"Mozilla/5.0 (Macintosh; Intel Mac OS X 10.15; rv:121.0) Gecko/20100101 Firefox/121.0",
	"Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
}

var positiveKeys = []string{
	"comment", "content", "text", "body", "message", "post", "reply",
}

var negativeKeys = []string{
	"contact", "support", "поиск", "search", "subscribe", "newsletter", "login", "signin", "checkout",
}

var (
	crowdParamPRX    = regexp.MustCompile(`[?&]p=\d+`)
	crowdParamPostRX = regexp.MustCompile(`[?&]post=\d+`)
	crowdParamIDRX   = regexp.MustCompile(`[?&]id=\d+`)
	crowdYearRX      = regexp.MustCompile(`/\d{4}/`)
	enDate1RX        = regexp.MustCompile(`\b([a-z]+)\s+([0-3]?\d),\s+(20\d{2})\b`)
	enDate2RX        = regexp.MustCompile(`\b([0-3]?\d)\s+([a-z]+)\s+(20\d{2})\b`)
	ruDateRX         = regexp.MustCompile(`\b([0-3]?\d)\s+([a-zа-яё]+)\s+(20\d{2})\b`)
	isoDateRX        = regexp.MustCompile(`\b(20\d{2})-(0[1-9]|1[0-2])-(0[1-9]|[12]\d|3[01])\b`)
)

// ====================== Config & Models ======================

type Config struct {
	MaxDepth           int
	MaxConcurrency     int
	RequestsPerSecond  float64
	PerHostRPS         float64
	TimeoutSeconds     int
	MaxPageSizeBytes   int
	MaxLinksPerDomain  int
	MaxPagesPerDomain  int
	AllowSubdomainWWW  bool
	CheckpointPath     string
	FindingsPath       string
	TargetsPath        string
	AntibotPath        string
	CheckpointInterval int
	MaxContentAgeDays  int
	VeryOldDays        int
	HostBackoffMS      int
	ProgressEverySec   int

	WidenOnSparse        bool
	SparseProbePages     int
	SparseFindsThreshold int
	WidenPagesCap        int
}

func defaultConfig() Config {
	return Config{
		MaxDepth:           10,
		MaxConcurrency:     16,
		RequestsPerSecond:  8.0,
		PerHostRPS:         0.5,
		TimeoutSeconds:     12,
		MaxPageSizeBytes:   6 * 1024 * 1024,
		MaxLinksPerDomain:  200,
		MaxPagesPerDomain:  100,
		AllowSubdomainWWW:  true,
		CheckpointPath:     "checkpoint.json",
		FindingsPath:       "crowd_findings.jsonl",
		TargetsPath:        "targets.txt",
		AntibotPath:        "antibot_domains.jsonl",
		CheckpointInterval: 60,
		MaxContentAgeDays:  1095,
		VeryOldDays:        0,
		HostBackoffMS:      1000,
		ProgressEverySec:   30,

		WidenOnSparse:        true,
		SparseProbePages:     60,
		SparseFindsThreshold: 2,
		WidenPagesCap:        800,
	}
}

type Finding struct {
	Domain                  string   `json:"domain"`
	URL                     string   `json:"url"`
	Depth                   int      `json:"depth"`
	Classification          string   `json:"class"`
	Priority                int      `json:"priority"`
	Timestamp               string   `json:"ts"`
	FormAction              string   `json:"form_action,omitempty"`
	FormActionResolved      string   `json:"form_action_resolved,omitempty"`
	FormMethod              string   `json:"form_method,omitempty"`
	HasTextarea             bool     `json:"has_textarea"`
	HasSubmit               bool     `json:"has_submit"`
	DetectedPlatformSignals []string `json:"signals,omitempty"`
	ContentDateISO          string   `json:"content_date,omitempty"`
	Notes                   string   `json:"notes,omitempty"`
}

type DomainResult struct {
	Domain   string
	Findings []*Finding
	Error    error
}

type Checkpoint struct {
	Processed map[string]bool `json:"processed"`
	Pos       int             `json:"pos"`
}

// ====================== Crawler Core ======================

type Crawler struct {
	cfg Config

	client    *FastClient
	semaphore chan struct{}

	// outputs
	resF     *os.File
	resBw    *bufio.Writer
	tgtF     *os.File
	tgtBw    *bufio.Writer
	resultMu sync.Mutex

	// checkpoint
	ckMu       sync.Mutex
	checkpoint *Checkpoint

	// trackers / dedup
	tracker FormTracker
	targets sync.Map

	// stats
	startTime        time.Time
	lastCheckpointAt time.Time
	lastProgressAt   time.Time

	processedDomains int64
	foundForms       int64
	errorsCount      int64
	targetsCount     int64
	sysErrPages      int64

	// diagnostics
	errorKinds sync.Map // map[string]*int64

	// minimal counters for report
	contactsSkipped int64
	authSkipped     int64
}

// ====================== HTTP Client ======================

// ====================== HTTP Client (ЗАМЕНА ЦЕЛОГО БЛОКА) ======================

type FastClient struct {
	hcH2         *http.Client
	hcH1         *http.Client
	rateLimiter  *rate.Limiter
	bytesRead    int64
	requests     int64
	maxBytes     int
	h1only       sync.Map
	hostLimiters sync.Map
	perHostRate  float64

	// Anti-detection additions
	userAgents []string
	uaIndex    int64
	sessions   sync.Map // map[string]*SessionData
}

type SessionData struct {
	mu           sync.RWMutex
	cookies      []*http.Cookie
	lastRequest  time.Time
	requestCount int64
	fingerprint  string
	userAgent    string
}

func NewFastClient(cfg Config) *FastClient {
	trH2 := &http.Transport{
		Proxy:               http.ProxyFromEnvironment,
		MaxIdleConns:        1024,
		MaxIdleConnsPerHost: 64,
		IdleConnTimeout:     30 * time.Second,
		ForceAttemptHTTP2:   runtime.GOOS != "windows",
		TLSClientConfig: &tls.Config{
			InsecureSkipVerify: false,
			MinVersion:         tls.VersionTLS12,
			CipherSuites: []uint16{
				tls.TLS_AES_128_GCM_SHA256,
				tls.TLS_AES_256_GCM_SHA384,
				tls.TLS_CHACHA20_POLY1305_SHA256,
				tls.TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
				tls.TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
				tls.TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
				tls.TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
			},
		},
	}

	trH1 := &http.Transport{
		Proxy:               http.ProxyFromEnvironment,
		MaxIdleConns:        1024,
		MaxIdleConnsPerHost: 64,
		IdleConnTimeout:     30 * time.Second,
		ForceAttemptHTTP2:   false,
		TLSNextProto:        map[string]func(string, *tls.Conn) http.RoundTripper{},
		TLSClientConfig: &tls.Config{
			InsecureSkipVerify: false,
			MinVersion:         tls.VersionTLS12,
		},
	}

	h2 := &http.Client{Transport: trH2, Timeout: time.Duration(cfg.TimeoutSeconds) * time.Second}
	h1 := &http.Client{Transport: trH1, Timeout: time.Duration(cfg.TimeoutSeconds) * time.Second}
	lim := rate.NewLimiter(rate.Limit(cfg.RequestsPerSecond), int(math.Max(1, cfg.RequestsPerSecond)))

	return &FastClient{
		hcH2:        h2,
		hcH1:        h1,
		rateLimiter: lim,
		maxBytes:    cfg.MaxPageSizeBytes,
		userAgents:  defaultUserAgents,
		perHostRate: cfg.PerHostRPS,
	}
}

func (fc *FastClient) getSessionData(host string) *SessionData {
	if v, ok := fc.sessions.Load(host); ok {
		return v.(*SessionData)
	}

	idx := atomic.AddInt64(&fc.uaIndex, 1)
	ua := fc.userAgents[idx%int64(len(fc.userAgents))]
	session := &SessionData{
		cookies:      []*http.Cookie{},
		lastRequest:  time.Now(),
		requestCount: 0,
		fingerprint:  fc.generateFingerprint(host),
		userAgent:    ua,
	}

	fc.sessions.Store(host, session)
	return session
}

func (fc *FastClient) getHostLimiter(host string) *rate.Limiter {
	if host == "" {
		return rate.NewLimiter(rate.Limit(fc.perHostRate), 1)
	}
	if v, ok := fc.hostLimiters.Load(host); ok {
		return v.(*rate.Limiter)
	}
	lim := rate.NewLimiter(rate.Limit(fc.perHostRate), 1)
	fc.hostLimiters.Store(host, lim)
	return lim
}

func (fc *FastClient) generateFingerprint(host string) string {
	// Simple fingerprint based on host and timestamp
	h := fnv.New64a()
	h.Write([]byte(host + time.Now().Format("2006-01-02")))
	return fmt.Sprintf("%x", h.Sum64())
}

// Добавляем недостающую функцию
func looksLikeHTTP2FramingErr(err error) bool {
	if err == nil {
		return false
	}
	errStr := strings.ToLower(err.Error())
	return strings.Contains(errStr, "http2") &&
		(strings.Contains(errStr, "frame") ||
			strings.Contains(errStr, "stream") ||
			strings.Contains(errStr, "protocol"))
}

type FetchResult struct {
	Status  int
	Headers http.Header
	Body    []byte
	URL     string
}

func (fc *FastClient) GetEx(ctx context.Context, rawURL string) (*FetchResult, error) {
	u, _ := url.Parse(rawURL)
	host := ""
	if u != nil {
		host = u.Hostname()
	}

	if err := fc.rateLimiter.Wait(ctx); err != nil {
		return nil, err
	}
	hl := fc.getHostLimiter(host)
	if err := hl.Wait(ctx); err != nil {
		return nil, err
	}

	// Get or create session for this host
	session := fc.getSessionData(host)

	session.mu.Lock()
	atomic.AddInt64(&session.requestCount, 1)

	// Add human-like delay between requests to same host
	timeSinceLastReq := time.Since(session.lastRequest)
	minDelay := time.Duration(500+rand.Intn(1000)) * time.Millisecond
	if timeSinceLastReq < minDelay {
		session.mu.Unlock()
		time.Sleep(minDelay - timeSinceLastReq)
		session.mu.Lock()
	}
	session.lastRequest = time.Now()
	session.mu.Unlock()

	client := fc.hcH2
	if v, ok := fc.h1only.Load(host); ok && v.(bool) {
		client = fc.hcH1
	}

	req, err := http.NewRequestWithContext(ctx, "GET", rawURL, nil)
	if err != nil {
		return nil, err
	}

	// Enhanced headers to mimic real browser
	fc.setRealisticHeaders(req, host, session)

	start := time.Now()
	resp, err := client.Do(req)
	ttfb := time.Since(start)
	if err != nil && client == fc.hcH2 && looksLikeHTTP2FramingErr(err) && host != "" {
		fc.h1only.Store(host, true)
		req2, e2 := http.NewRequestWithContext(ctx, "GET", rawURL, nil)
		if e2 != nil {
			return nil, e2
		}
		fc.setRealisticHeaders(req2, host, session)
		start = time.Now()
		resp, err = fc.hcH1.Do(req2)
		ttfb = time.Since(start)
	}

	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()

	// Adapt host rate based on response
	if resp.StatusCode == 429 || resp.StatusCode == 503 {
		hl.SetLimit(0.1)
	} else {
		current := hl.Limit()
		if ttfb > 1500*time.Millisecond {
			hl.SetLimit(rate.Limit(math.Max(0.1, float64(current)/2)))
		} else if ttfb < 500*time.Millisecond && current < rate.Limit(fc.perHostRate) {
			hl.SetLimit(rate.Limit(math.Min(fc.perHostRate, float64(current)+0.1)))
		}
	}

	// Store cookies for session persistence
	if len(resp.Cookies()) > 0 {
		session.mu.Lock()
		session.cookies = mergeCookies(session.cookies, resp.Cookies())
		session.mu.Unlock()
	}

	atomic.AddInt64(&fc.requests, 1)
	lr := io.LimitReader(resp.Body, int64(fc.maxBytes)+1)
	body, _ := io.ReadAll(lr)
	if len(body) > fc.maxBytes {
		body = body[:fc.maxBytes]
	}
	atomic.AddInt64(&fc.bytesRead, int64(len(body)))

	return &FetchResult{
		Status:  resp.StatusCode,
		Headers: resp.Header.Clone(),
		Body:    body,
		URL:     resp.Request.URL.String(),
	}, nil
}

func (fc *FastClient) setRealisticHeaders(req *http.Request, host string, session *SessionData) {
	userAgent := session.userAgent

	req.Header.Set("User-Agent", userAgent)

	req.Header.Set("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7")
	req.Header.Set("Accept-Language", "en-US,en;q=0.9,ru;q=0.8")
	req.Header.Set("Accept-Encoding", "gzip, deflate")
	req.Header.Set("Cache-Control", "max-age=0")
	req.Header.Set("Sec-Fetch-Dest", "document")
	req.Header.Set("Sec-Fetch-Mode", "navigate")
	req.Header.Set("Sec-Fetch-Site", "none")
	req.Header.Set("Sec-Fetch-User", "?1")
	req.Header.Set("Upgrade-Insecure-Requests", "1")

	// Add DNT header occasionally
	if rand.Intn(3) == 0 {
		req.Header.Set("DNT", "1")
	}

	// Set referer for non-first requests
	session.mu.RLock()
	reqCount := session.requestCount
	session.mu.RUnlock()

	if reqCount > 1 && rand.Intn(2) == 0 {
		req.Header.Set("Referer", "https://"+host+"/")
	}

	// Add session cookies with basic validation
	session.mu.RLock()
	for _, cookie := range session.cookies {
		// Простая проверка домена
		if cookie.Domain == "" || cookie.Domain == host || strings.HasSuffix(host, cookie.Domain) {
			if cookie.Expires.IsZero() || cookie.Expires.After(time.Now()) {
				req.AddCookie(cookie)
			}
		}
	}
	session.mu.RUnlock()

	// Vary some headers based on user agent
	if strings.Contains(userAgent, "Chrome") {
		req.Header.Set("Sec-Ch-Ua", `"Not_A Brand";v="8", "Chromium";v="120", "Google Chrome";v="120"`)
		req.Header.Set("Sec-Ch-Ua-Mobile", "?0")
		req.Header.Set("Sec-Ch-Ua-Platform", `"Windows"`)
	} else if strings.Contains(userAgent, "Firefox") {
		// Firefox doesn't send Sec-Ch-Ua headers
		req.Header.Del("Sec-Ch-Ua")
		req.Header.Del("Sec-Ch-Ua-Mobile")
		req.Header.Del("Sec-Ch-Ua-Platform")
	}
}

// ====================== НОВЫЙ БЛОК: Utils для Content-Type ======================

func isHTMLContent(contentType string) bool {
	ct := strings.ToLower(contentType)
	return strings.Contains(ct, "text/html") || strings.Contains(ct, "application/xhtml+xml")
}

// ====================== Entry ======================

func main() {
	flag.Usage = func() {
		fmt.Fprintf(os.Stderr, "Usage: %s domains.txt\n", filepath.Base(os.Args[0]))
	}
	flag.Parse()
	if flag.NArg() != 1 {
		flag.Usage()
		os.Exit(2)
	}
	listPath := flag.Arg(0)

	cfg := defaultConfig()
	_ = writeLines("user_agents.txt", defaultUserAgents)
	_ = writeLines("positive_keys.txt", positiveKeys)
	_ = writeLines("negative_keys.txt", negativeKeys)
	c := &Crawler{
		cfg:       cfg,
		client:    NewFastClient(cfg),
		semaphore: make(chan struct{}, cfg.MaxConcurrency),
	}
	if err := c.Run(listPath); err != nil {
		log.Fatalf("fatal: %v", err)
	}
}

// ====================== Orchestration ======================

func (c *Crawler) Run(listPath string) error {
	c.startTime = time.Now()
	c.lastCheckpointAt = c.startTime
	c.lastProgressAt = c.startTime

	if err := c.initResultFile(); err != nil {
		return err
	}
	defer c.closeResultFile()

	c.checkpoint = c.loadCheckpoint()

	log.Printf("Starting crawler: MaxDepth=%d, Concurrency=%d, RPS=%.1f, MaxAgeDays=%d, PerDomainMax=%d",
		c.cfg.MaxDepth, c.cfg.MaxConcurrency, c.cfg.RequestsPerSecond, c.cfg.MaxContentAgeDays, c.cfg.MaxLinksPerDomain)
	if c.checkpoint != nil && c.checkpoint.Pos > 0 {
		log.Printf("Loaded checkpoint: %d processed domains", len(c.checkpoint.Processed))
	}

	f, err := os.Open(listPath)
	if err != nil {
		return err
	}
	defer f.Close()

	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 0, 1024*1024), 1024*1024)

	pos := 0
	if c.checkpoint != nil {
		pos = c.checkpoint.Pos
	}

	checkpointEvery := time.Duration(c.cfg.CheckpointInterval) * time.Second
	if checkpointEvery <= 0 {
		checkpointEvery = 60 * time.Second
	}
	progressEvery := time.Duration(c.cfg.ProgressEverySec) * time.Second
	if progressEvery <= 0 {
		progressEvery = 30 * time.Second
	}

	for i := 0; sc.Scan(); i++ {
		if i < pos {
			continue
		}
		line := strings.TrimSpace(sc.Text())
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		domain := normalizeDomainLine(line)
		if domain == "" {
			continue
		}
		if c.checkpoint != nil && c.checkpoint.Processed[domain] {
			continue
		}

		c.semaphore <- struct{}{}
		go func(dom string, index int) {
			defer func() { <-c.semaphore }()
			res := c.processDomain(dom)
			if len(res.Findings) > 0 {
				c.writeFindings(res.Findings)
			}
			if res.Error != nil {
				atomic.AddInt64(&c.errorsCount, 1)
			}
			atomic.AddInt64(&c.processedDomains, 1)

			// checkpoint mark
			c.ckMu.Lock()
			if c.checkpoint != nil {
				c.checkpoint.Processed[dom] = true
				c.checkpoint.Pos = index + 1
			}
			c.ckMu.Unlock()
		}(domain, i)

		// periodic progress
		if time.Since(c.lastProgressAt) >= progressEvery {
			c.printStats()
			c.lastProgressAt = time.Now()
		}
		// periodic checkpoint + every 250 domains
		if time.Since(c.lastCheckpointAt) >= checkpointEvery || (i%250 == 0 && i > pos) {
			c.saveCheckpoint(i + 1)
			c.lastCheckpointAt = time.Now()
		}
	}

	// drain
	for i := 0; i < cap(c.semaphore); i++ {
		c.semaphore <- struct{}{}
	}

	c.printFinalStats()
	return nil
}

// ====================== Domain Crawl (Frontier) ======================
func (c *Crawler) processDomain(domain string) *DomainResult {
	res := &DomainResult{Domain: domain}
	starts := []string{"https://" + domain, "http://" + domain}
	var baseURL string
	var baseFetch *FetchResult

	hostNextAt := make(map[string]time.Time)
	hostGap := time.Duration(c.cfg.HostBackoffMS) * time.Millisecond
	waitHost := func(rawURL string) {
		u, err := url.Parse(rawURL)
		if err != nil {
			return
		}
		if until, ok := hostNextAt[u.Host]; ok {
			now := time.Now()
			if now.Before(until) {
				time.Sleep(until.Sub(now))
			}
		}
	}
	markHost := func(rawURL string) {
		u, err := url.Parse(rawURL)
		if err != nil {
			return
		}
		hostNextAt[u.Host] = time.Now().Add(hostGap)
	}

	for _, u := range starts {
		ctx, cancel := context.WithTimeout(context.Background(), time.Duration(c.cfg.TimeoutSeconds)*time.Second)
		waitHost(u)
		fr, err := c.client.GetEx(ctx, u)
		cancel()
		markHost(u)
		if err != nil || fr == nil || len(fr.Body) < 64 {
			c.bumpError("base_fetch")
			continue
		}
		ct := strings.ToLower(strings.Join(fr.Headers.Values("Content-Type"), " "))
		if !isHTMLContent(ct) {
			c.bumpError("non_html_base")
			continue
		}
		if isSystemErrorPage(fr.Body) {
			atomic.AddInt64(&c.sysErrPages, 1)
			c.bumpError("system_error_page")
			continue
		}

		if fr.Status == 429 || fr.Status == 503 {
			retryAfter := fr.Headers.Get("Retry-After")
			delay := 8 * time.Second
			if retryAfter != "" {
				if n, e := strconv.Atoi(strings.TrimSpace(retryAfter)); e == nil && n > 0 {
					delay = time.Duration(n) * time.Second
				} else if t, e := http.ParseTime(retryAfter); e == nil {
					if dd := time.Until(t); dd > 0 {
						delay = dd
					}
				}
			}
			uParsed, _ := url.Parse(u)
			if uParsed != nil {
				hostNextAt[uParsed.Host] = time.Now().Add(delay)
			}
			continue
		}

		if isAntiBot(fr.Status, fr.Headers, fr.Body) {
			c.writeAntibot(domain, fmt.Sprintf("base:%s status=%d", u, fr.Status))
			if uu, err := url.Parse(u); err == nil {
				hostNextAt[uu.Host] = time.Now().Add(5 * time.Minute)
			}
			continue
		}
		baseURL, baseFetch = u, fr
		break
	}
	if baseURL == "" {
		res.Error = fmt.Errorf("no base fetch")
		return res
	}

	type qitem struct {
		url   string
		depth int
	}
	hi := []qitem{{baseURL, 0}}
	me := []qitem{}
	lo := []qitem{}
	pop := func() (qitem, bool) {
		if len(hi) > 0 {
			it := hi[0]
			hi = hi[1:]
			return it, true
		}
		if len(me) > 0 {
			it := me[0]
			me = me[1:]
			return it, true
		}
		if len(lo) > 0 {
			it := lo[0]
			lo = lo[1:]
			return it, true
		}
		return qitem{}, false
	}
	push := func(u string, d int) {
		if d > c.cfg.MaxDepth {
			return
		}
		if hasCrowdURL(u) || d == 0 {
			hi = append(hi, qitem{u, d})
			return
		}
		l := strings.ToLower(u)
		if strings.Contains(l, "/blog/") || strings.Contains(l, "/news/") || strings.Contains(l, "/20") || strings.Contains(l, "#respond") {
			me = append(me, qitem{u, d})
			return
		}
		lo = append(lo, qitem{u, d})
	}

	visited := make(map[string]bool)
	found := 0
	maxFound := c.cfg.MaxLinksPerDomain
	if maxFound <= 0 {
		maxFound = 500
	}
	pageBudget := c.cfg.MaxPagesPerDomain
	if pageBudget <= 0 {
		pageBudget = 200
	}
	pages := 0
	allowed := map[string]bool{domain: true}
	if c.cfg.AllowSubdomainWWW {
		allowed["www."+domain] = true
	}

	for found < maxFound && pages < pageBudget {
		item, ok := pop()
		if !ok {
			break
		}
		if visited[item.url] {
			continue
		}

		var fr *FetchResult
		var err error
		if item.url == baseURL {
			fr = baseFetch
		} else {
			ctx, cancel := context.WithTimeout(context.Background(), time.Duration(c.cfg.TimeoutSeconds)*time.Second)
			waitHost(item.url)
			fr, err = c.client.GetEx(ctx, item.url)
			cancel()
			markHost(item.url)
			if err != nil || fr == nil || len(fr.Body) < 64 {
				c.bumpError("fetch")
				visited[item.url] = true
				continue
			}
		}
		pages++

		if fr.Status == 429 || fr.Status == 503 {
			retryAfter := fr.Headers.Get("Retry-After")
			delay := 8 * time.Second
			if retryAfter != "" {
				if n, e := strconv.Atoi(strings.TrimSpace(retryAfter)); e == nil && n > 0 {
					delay = time.Duration(n) * time.Second
				} else if t, e := http.ParseTime(retryAfter); e == nil {
					dd := time.Until(t)
					if dd > 0 {
						delay = dd
					}
				}
			}
			u, _ := url.Parse(item.url)
			if u != nil {
				hostNextAt[u.Host] = time.Now().Add(delay)
			}
			push(item.url, item.depth)
			continue
		}

		ct := strings.ToLower(strings.Join(fr.Headers.Values("Content-Type"), " "))
		if !isHTMLContent(ct) {
			c.bumpError("non_html_page")
			visited[item.url] = true
			continue
		}
		if isSystemErrorPage(fr.Body) {
			atomic.AddInt64(&c.sysErrPages, 1)
			c.bumpError("system_error_page")
			visited[item.url] = true
			continue
		}
		if isAntiBot(fr.Status, fr.Headers, fr.Body) {
			c.writeAntibot(domain, fmt.Sprintf("crawl:%s status=%d", item.url, fr.Status))
			u, _ := url.Parse(item.url)
			if u != nil {
				hostNextAt[u.Host] = time.Now().Add(5 * time.Minute)
			}
			push(item.url, item.depth)
			continue
		}

		doc, err := goquery.NewDocumentFromReader(bytes.NewReader(fr.Body))
		if err != nil {
			c.bumpError("parse")
			visited[item.url] = true
			continue
		}
		visited[item.url] = true

		signals := detectPlatformSignals(fr.Headers, fr.Body)
		var dateISO string
		var isOld bool
		var isVeryOld bool
		if c.cfg.MaxContentAgeDays > 0 || c.cfg.VeryOldDays > 0 {
			if dt, ok := detectContentDate(doc, fr.Body); ok {
				dateISO = dt.UTC().Format(time.RFC3339)
				if c.cfg.VeryOldDays > 0 && dt.Before(time.Now().AddDate(0, 0, -c.cfg.VeryOldDays)) {
					isVeryOld = true
				} else if c.cfg.MaxContentAgeDays > 0 && dt.Before(time.Now().AddDate(0, 0, -c.cfg.MaxContentAgeDays)) {
					isOld = true
				}
			}
		}

		// Пропускаем очень старый контент
		if isVeryOld {
			continue
		}

		finds := c.findFormsOnPage(doc, item.url, item.depth, signals, dateISO, isOld)
		if len(finds) > 0 {
			var uniq []*Finding
			for _, f := range finds {
				h := c.generateFindingHash(f)
				if c.tracker.Add(h) {
					uniq = append(uniq, f)
				}
			}
			if len(uniq) > 0 {
				res.Findings = append(res.Findings, uniq...)
				atomic.AddInt64(&c.foundForms, int64(len(uniq)))
				found += len(uniq)
				if found >= maxFound {
					break
				}
			}
		}

		links := c.extractLinks(doc, item.url, domain, allowed)
		if len(links) > 0 && item.depth+1 <= c.cfg.MaxDepth {
			for _, u := range links {
				push(u, item.depth+1)
			}
		}

		if c.cfg.WidenOnSparse && pages >= c.cfg.SparseProbePages && found < c.cfg.SparseFindsThreshold && pageBudget < c.cfg.WidenPagesCap {
			pageBudget = c.cfg.WidenPagesCap
		}
	}
	return res
}

// ====================== Page Analysis (forms only) ======================

func (c *Crawler) findFormsOnPage(doc *goquery.Document, pageURL string, depth int, signals []string, dateISO string, isOld bool) []*Finding {
	var out []*Finding

	doc.Find("form").Each(func(i int, form *goquery.Selection) {
		// primary UGC gate — есть ли реальная зона ввода?
		if !hasPrimaryUGC(form) {
			return
		}

		// negative filters — минимальные и строгие
		if isContactForm(form) {
			atomic.AddInt64(&c.contactsSkipped, 1)
			return
		}
		if isSearchForm(form) || isNewsletterForm(form) || isEcommerceForm(form, pageURL) {
			return
		}
		// чистая auth-форма без UGC — skip
		if isAuthForm(form, pageURL) && !hasPrimaryUGC(form) {
			atomic.AddInt64(&c.authSkipped, 1)
			return
		}

		class := classifyUGC(form, pageURL)
		if class == "" {
			return
		}

		action, _ := form.Attr("action")
		method := strings.ToUpper(strings.TrimSpace(attrOr(form, "method", "GET")))
		hasTextarea := form.Find("textarea").Length() > 0
		hasSubmit := form.Find("input[type=submit], button[type=submit], button:not([type])").Length() > 0

		priority := classificationPriority(class)
		if isOld {
			priority++
		}

		resolved := resolveAction(pageURL, action)

		out = append(out, &Finding{
			Domain:                  extractDomain(pageURL),
			URL:                     pageURL,
			Depth:                   depth,
			Classification:          class,
			Priority:                priority,
			Timestamp:               time.Now().UTC().Format(time.RFC3339),
			FormAction:              action,
			FormActionResolved:      resolved,
			FormMethod:              method,
			HasTextarea:             hasTextarea,
			HasSubmit:               hasSubmit,
			DetectedPlatformSignals: dedupStrings(signals),
			ContentDateISO:          dateISO,
		})
	})

	return out
}

// ---------------------- Positive gate ----------------------

func hasPrimaryUGC(form *goquery.Selection) bool {
	// 1) textarea + (name id hints OR intent)
	if form.Find("textarea").Length() > 0 {
		nameHint := form.Find(`textarea[name*=comment], textarea[name*=content], textarea[name*=text], textarea[name*=body], textarea[name*=message], #comment`).Length() > 0
		if nameHint || formHasUGCIntent(form) {
			return true
		}
	}
	// 2) title+textarea
	if form.Find("input[name*=title], input[name=post_title], input[name*=subject], input[name*=topic_title]").Length() > 0 &&
		form.Find("textarea").Length() > 0 {
		return true
	}
	// 3) WP comments markers
	if form.Is("#commentform") || form.Find("#respond").Length() > 0 ||
		form.Find("input[name=comment_post_ID], input[name=comment_parent]").Length() > 0 ||
		form.Find("textarea[name=comment]").Length() > 0 {
		return true
	}
	// 4) reviews
	if isReviewForm(form) && form.Find("textarea").Length() > 0 {
		return true
	}
	return false
}

func formHasUGCIntent(form *goquery.Selection) bool {
	check := func(s string) bool {
		s = strings.ToLower(s)
		keys := []string{
			"comment", "коммент", "ответить", "reply",
			"post comment", "send comment", "add comment", "leave a comment",
			"create topic", "new topic", "start discussion", "start thread",
			"опубликовать", "опубликовать комментарий", "добавить тему", "оставить отзыв",
		}
		for _, k := range keys {
			if strings.Contains(s, k) {
				return true
			}
		}
		return false
	}
	ok := false
	form.Find("button, input[type=submit]").Each(func(_ int, el *goquery.Selection) {
		if t := strings.TrimSpace(el.Text()); t != "" && check(t) {
			ok = true
			return
		}
		if v, exists := el.Attr("value"); exists && check(v) {
			ok = true
			return
		}
		if id, exists := el.Attr("id"); exists && check(id) {
			ok = true
			return
		}
		if name, exists := el.Attr("name"); exists && check(name) {
			ok = true
			return
		}
		if cls, exists := el.Attr("class"); exists && check(cls) {
			ok = true
			return
		}
	})
	if ok {
		return true
	}
	return check(form.Text())
}

// ---------------------- Negative filters ----------------------

func isContactForm(form *goquery.Selection) bool {
	// не трогаем явные комменты/отзывы
	if form.Is("#commentform") || form.Find("#comment, textarea[name=comment]").Length() > 0 {
		return false
	}
	if isReviewForm(form) {
		return false
	}

	html, _ := form.Html()
	l := strings.ToLower(html)
	txt := strings.ToLower(form.Text())

	// популярные конструкторы контакт-форм
	if strings.Contains(l, "wpcf7") || strings.Contains(l, "wpcf7-form") || // Contact Form 7
		strings.Contains(l, "wpforms-form") || // WPForms
		strings.Contains(l, "gform_wrapper") || strings.Contains(l, "gform_body") || // Gravity
		strings.Contains(l, "nf-form") || strings.Contains(l, "nf-form-cont") || // Ninja
		strings.Contains(l, "et_pb_contact_form") || // Divi
		strings.Contains(l, "grunion-contact-form") || // Jetpack
		strings.Contains(l, "elementor-form") || // Elementor
		strings.Contains(l, "forminator-ui") || // Forminator
		strings.Contains(l, "caldera-grid") || // Caldera
		(strings.Contains(l, "contact-form") && !strings.Contains(l, "comment-form")) {
		return true
	}

	// состав полей: email/tel + subject + textarea
	emailCnt := form.Find("input[type=email], input[name*=email]").Length()
	phoneCnt := form.Find("input[type=tel], input[name*=phone], input[name*=tel]").Length()
	subjCnt := form.Find("input[name*=subject], input[id*=subject]").Length()
	msgArea := form.Find("textarea").Length()
	if msgArea > 0 && (emailCnt+phoneCnt >= 1) && subjCnt >= 1 {
		return true
	}

	// тексты
	if strings.Contains(txt, "contact") || strings.Contains(txt, "support") || strings.Contains(txt, "обратная связь") ||
		strings.Contains(txt, "связаться") || strings.Contains(txt, "напишите нам") ||
		strings.Contains(txt, "send message") || strings.Contains(txt, "send us a message") ||
		strings.Contains(txt, "отправить сообщение") {
		return true
	}
	return false
}

func isSearchForm(form *goquery.Selection) bool {
	if form.Find("input[type=search]").Length() > 0 {
		return true
	}
	if r, ok := form.Attr("role"); ok && strings.EqualFold(r, "search") {
		return true
	}
	ph := strings.ToLower(strings.Join(attrValues(form, "placeholder"), " "))
	return strings.Contains(ph, "search") || strings.Contains(ph, "поиск")
}

func isNewsletterForm(form *goquery.Selection) bool {
	if form.Find("textarea").Length() > 0 {
		return false
	}
	if form.Find("input[type=email], input[name*=email]").Length() == 0 {
		return false
	}
	h, _ := form.Html()
	l := strings.ToLower(h)
	return strings.Contains(l, "newsletter") || strings.Contains(l, "subscribe") || strings.Contains(l, "mailchimp")
}

func isEcommerceForm(form *goquery.Selection, pageURL string) bool {
	lp := strings.ToLower(pageURL)
	h, _ := form.Html()
	l := strings.ToLower(h)

	if strings.Contains(lp, "checkout") || strings.Contains(lp, "cart") || strings.Contains(lp, "basket") || strings.Contains(lp, "payment") {
		return true
	}
	if strings.Contains(l, "checkout") || strings.Contains(l, "add-to-cart") || strings.Contains(l, "woocommerce") || strings.Contains(l, "payment") {
		return true
	}
	return false
}

func isAuthForm(form *goquery.Selection, pageURL string) bool {
	if form.Find("input[type=password]").Length() > 0 {
		return true
	}
	if looksLikeAuthURL(pageURL) {
		return true
	}
	if act, ok := form.Attr("action"); ok && looksLikeAuthURL(act) {
		return true
	}
	return false
}

func looksLikeAuthURL(u string) bool {
	lu := strings.ToLower(u)
	keys := []string{"login", "signin", "register", "signup", "auth", "wp-login"}
	for _, k := range keys {
		if strings.Contains(lu, k) {
			return true
		}
	}
	return false
}

// ---------------------- Classification ----------------------

func classifyUGC(form *goquery.Selection, pageURL string) string {
	lpage := strings.ToLower(pageURL)

	// comments
	if form.Is("#commentform") || form.Find("#respond").Length() > 0 ||
		form.Find("textarea[name=comment], #comment").Length() > 0 ||
		form.Find("input[name=comment_post_ID], input[name=comment_parent]").Length() > 0 {
		return "comments"
	}

	// forum (WP + классические)
	// WP forums
	if form.Find("input[name*=topic], input[name*=subject], input[name*=title]").Length() > 0 &&
		form.Find("textarea").Length() > 0 &&
		(form.Find(".bbp-form, #bbp-topic-form, #bbp-reply-form, .wpforo-wrap").Length() > 0 ||
			crowdPathRX.MatchString(lpage)) {
		return "forum"
	}
	// classic engines: phpBB/vBulletin/SMF/MyBB
	if form.Find("textarea[name=message]").Length() > 0 {
		hints := []string{
			"posting.php?mode=post", "posting.php?mode=reply", "viewtopic.php",
			"showthread.php", "newreply.php", "newthread.php",
			"index.php?action=post", "index.php?action=post2",
		}
		for _, h := range hints {
			if strings.Contains(lpage, h) {
				return "forum"
			}
		}
	}

	// article-submit
	if (form.Find("input[name=post_title], input[name*=title]").Length() > 0 &&
		form.Find("textarea[name=content], textarea[name*=content], textarea[name*=post]").Length() > 0) ||
		form.Find(".wp-editor-area").Length() > 0 {
		return "article-submit"
	}

	// guestbook
	if strings.Contains(lpage, "guestbook") && form.Find("textarea").Length() > 0 {
		return "guestbook"
	}

	// review
	if isReviewForm(form) && form.Find("textarea").Length() > 0 {
		return "review"
	}

	// generic blog UGC
	if hasPrimaryUGC(form) {
		return "blog"
	}
	return ""
}

func isReviewForm(form *goquery.Selection) bool {
	if form.Find("input[name*=rating], select[name*=rating]").Length() > 0 {
		return true
	}
	html, _ := form.Html()
	l := strings.ToLower(html)
	return strings.Contains(l, "woocommerce-review") || strings.Contains(l, "stars-rating") || strings.Contains(l, "star-rating")
}

func classificationPriority(class string) int {
	switch class {
	case "comments":
		return 0
	case "forum":
		return 1
	case "article-submit":
		return 2
	case "guestbook":
		return 3
	case "review":
		return 4
	case "blog":
		return 5
	default:
		return 6
	}
}

// ====================== URL / Links ======================

var (
	crowdDateRX1 = regexp.MustCompile(`/20\d{2}/(0[1-9]|1[0-2])/`) // /2023/05/
	crowdDateRX2 = regexp.MustCompile(`/\d{4}/\d{1,2}/`)           // /2023/5/
	crowdPathRX  = regexp.MustCompile(`forum|topic|thread|discussion|comment`)
)

func (c *Crawler) extractLinks(doc *goquery.Document, pageURL, domain string, allowed map[string]bool) []string {
	var out []string
	doc.Find("a[href]").Each(func(_ int, a *goquery.Selection) {
		href, _ := a.Attr("href")
		if href == "" {
			return
		}
		u, ok := normalizeURL(pageURL, href)
		if !ok || u == "" {
			return
		}
		uu, err := url.Parse(u)
		if err != nil {
			return
		}
		if !allowed[uu.Host] {
			return
		}
		// skip media/docs
		if skipFileExt(u) {
			return
		}
		// skip noisy paths
		lp := strings.ToLower(u)
		if strings.Contains(lp, "/wp-json") || strings.Contains(lp, "/wp-admin") ||
			strings.Contains(lp, "xmlrpc.php") || strings.HasSuffix(lp, ".xml") ||
			strings.Contains(lp, "/feed") || strings.Contains(lp, "/print") {
			return
		}
		// strip tracking
		sanitizeURLQuery(uu)
		u = uu.String()
		out = append(out, u)
	})
	return dedupStrings(out)
}

func hasCrowdURL(u string) bool {
	lu := strings.ToLower(u)

	// Более строгие паттерны дат
	if crowdDateRX1.MatchString(lu) || crowdDateRX2.MatchString(lu) {
		return true
	}

	// Строгие форумные паттерны
	hints := []string{
		"showthread", "viewtopic", "newreply", "newthread",
		"action=post", "mode=reply", "mode=post", "do=postreply",
		"/discussion/", "/community/", "/board/",
	}
	for _, h := range hints {
		if strings.Contains(lu, h) {
			return true
		}
	}

	// Специфические WordPress/CMS паттерны
	if strings.Contains(lu, "#respond") {
		return true
	}

	// Более строгие ID паттерны (только числовые)
	if crowdParamPRX.MatchString(lu) ||
		crowdParamPostRX.MatchString(lu) ||
		crowdParamIDRX.MatchString(lu) {
		return true
	}

	// Блог/новости только если есть численные индикаторы
	if (strings.Contains(lu, "/blog/") || strings.Contains(lu, "/news/")) &&
		(strings.Contains(lu, "/20") || crowdYearRX.MatchString(lu)) {
		return true
	}

	return false
}

func normalizeURL(baseURL, href string) (string, bool) {
	bu, err := url.Parse(baseURL)
	if err != nil {
		return "", false
	}
	u, err := url.Parse(href)
	if err != nil {
		return "", false
	}
	res := bu.ResolveReference(u)
	res.Fragment = ""
	// normalize tracking params
	sanitizeURLQuery(res)
	return res.String(), true
}

func sanitizeURLQuery(u *url.URL) {
	q := u.Query()
	for k := range q {
		kl := strings.ToLower(k)
		if strings.HasPrefix(kl, "utm_") || kl == "fbclid" || kl == "gclid" || kl == "yclid" || kl == "ref" || kl == "replytocom" {
			q.Del(k)
		}
	}
	u.RawQuery = q.Encode()
}

func skipFileExt(u string) bool {
	parsed, err := url.Parse(u)
	if err != nil {
		return false
	}

	path := strings.ToLower(parsed.Path)
	exts := []string{".jpg", ".jpeg", ".png", ".gif", ".webp", ".svg", ".ico",
		".pdf", ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx",
		".zip", ".rar", ".7z", ".mp3", ".mp4", ".avi", ".mov", ".mkv", ".webm"}

	for _, e := range exts {
		if strings.HasSuffix(path, e) {
			return true
		}
	}
	return false
}

// ====================== Signals / Anti-bot / Errors ======================

func detectPlatformSignals(h http.Header, body []byte) []string {
	var out []string
	server := strings.ToLower(strings.Join(h.Values("Server"), " "))
	powered := strings.ToLower(strings.Join(h.Values("X-Powered-By"), " "))
	lb := strings.ToLower(string(body))

	if strings.Contains(server, "nginx") {
		out = append(out, "nginx")
	}
	if strings.Contains(server, "apache") {
		out = append(out, "apache")
	}
	if strings.Contains(powered, "php") || strings.Contains(lb, "php") {
		out = append(out, "php")
	}
	if strings.Contains(lb, "wp-content") {
		out = append(out, "wordpress")
	}
	if strings.Contains(lb, "bbpress") {
		out = append(out, "bbpress")
	}
	if strings.Contains(lb, "wpforo") {
		out = append(out, "wpforo")
	}
	if strings.Contains(lb, "wpdiscuz") {
		out = append(out, "wpdiscuz")
	}
	if strings.Contains(lb, "disqus") {
		out = append(out, "disqus")
	}
	return dedupStrings(out)
}

func isAntiBot(status int, hdr http.Header, body []byte) bool {
	lb := strings.ToLower(string(body))
	server := strings.ToLower(strings.Join(hdr.Values("Server"), " "))

	// Status code checks (ИСПРАВЛЕНО: убрали 202)
	if status == 403 || status == 429 || status == 503 {
		return true
	}

	// Server header checks
	antibot_servers := []string{"cloudflare", "incapsula", "sucuri", "imperva", "akamai", "fastly"}
	for _, srv := range antibot_servers {
		if strings.Contains(server, srv) && (status >= 400 || containsAntibotContent(lb)) {
			return true
		}
	}

	// Enhanced content detection
	antibot_phrases := []string{
		"checking your browser", "attention required", "access denied",
		"__cf_chl", "jschl_answer", "ray id", "incap_ses",
		"distil_r_captcha", "sucuri", "blocked by", "security check",
		"verification required", "please wait", "loading...",
		"javascript required", "enable javascript", "browser check",
		"anti-bot", "bot protection", "captcha", "recaptcha",
		"hcaptcha", "turnstile", "challenge", "verify you are human",
		"pardon our interruption", "unusual traffic", "automated requests",
	}

	for _, phrase := range antibot_phrases {
		if strings.Contains(lb, phrase) {
			return true
		}
	}

	// Check for common antibot JavaScript patterns
	js_patterns := []string{
		"navigator.webdriver", "webdriver", "phantomjs", "headless",
		"selenium", "automation", "bot", "__nightmare",
		"_phantom", "callphantom", "__fxdriver_unwrapped",
	}

	for _, pattern := range js_patterns {
		if strings.Contains(lb, pattern) {
			return true
		}
	}

	// Check response headers (ИСПРАВЛЕНО: убрали server-timing из подозрительных)
	suspicious_headers := []string{"cf-ray", "x-sucuri-id", "x-iinfo"}
	for _, h := range suspicious_headers {
		if hdr.Get(h) != "" && status >= 400 {
			return true
		}
	}

	return false
}

func containsAntibotContent(content string) bool {
	// Heuristic: very short pages with specific keywords
	if len(content) < 2000 {
		keywords := []string{"challenge", "verification", "checking", "loading", "wait"}
		count := 0
		for _, kw := range keywords {
			if strings.Contains(content, kw) {
				count++
			}
		}
		return count >= 2
	}
	return false
}

func isSystemErrorPage(body []byte) bool {
	lb := strings.ToLower(string(body))
	errRX := []*regexp.Regexp{
		regexp.MustCompile(`не\s+удаётся\s+получить\s+доступ`),
		regexp.MustCompile(`this\s+site\s+can('t|not)\s+be\s+reached`),
		regexp.MustCompile(`file\s+not\s+found|cannot\s+access\s+the\s+file`),
		regexp.MustCompile(`ошибка\s+сервера|внутренняя\s+ошибка`),
		regexp.MustCompile(`temporarily\s+unavailable|connection\s+timed\s*out`),
		regexp.MustCompile(`service\s+unavailable|server\s+error`),
		regexp.MustCompile(`site\s+is\s+down|site\s+unavailable`),
	}
	for _, rx := range errRX {
		if rx.MatchString(lb) {
			return true
		}
	}
	return false
}

func (c *Crawler) bumpError(kind string) {
	vRaw, _ := c.errorKinds.LoadOrStore(kind, new(int64))
	v := vRaw.(*int64)
	atomic.AddInt64(v, 1)
}

// ====================== Dates ======================

var ruMonth = map[string]time.Month{
	"января": time.January, "февраля": time.February, "марта": time.March, "апреля": time.April,
	"мая": time.May, "июня": time.June, "июля": time.July, "августа": time.August,
	"сентября": time.September, "октября": time.October, "ноября": time.November, "декабря": time.December,
	"янв": time.January, "фев": time.February, "мар": time.March, "апр": time.April, "июн": time.June,
	"июл": time.July, "авг": time.August, "сен": time.September, "сент": time.September, "окт": time.October,
	"ноя": time.November, "дек": time.December,
}

func detectContentDate(doc *goquery.Document, body []byte) (time.Time, bool) {
	if m := doc.Find(`meta[property="article:published_time"]`); m.Length() > 0 {
		if v, ok := m.Attr("content"); ok {
			if t, err := time.Parse(time.RFC3339, strings.TrimSpace(v)); err == nil {
				return t, true
			}
		}
	}
	if t := doc.Find("time[datetime]"); t.Length() > 0 {
		if v, ok := t.Attr("datetime"); ok {
			if tt, err := time.Parse(time.RFC3339, strings.TrimSpace(v)); err == nil {
				return tt, true
			}
			if tt, err := time.Parse("2006-01-02", strings.TrimSpace(v)); err == nil {
				return tt, true
			}
		}
	}
	lb := strings.ToLower(string(body))
	if tt, ok := parseEnDate(lb); ok {
		return tt, true
	}
	if tt, ok := parseRuDate(lb); ok {
		return tt, true
	}
	if m := isoDateRX.FindStringSubmatch(lb); len(m) == 4 {
		if t, err := time.Parse("2006-01-02", m[1]+"-"+m[2]+"-"+m[3]); err == nil {
			return t, true
		}
	}
	return time.Time{}, false
}

func parseEnDate(lb string) (time.Time, bool) {
	months := map[string]time.Month{
		"january": time.January, "jan": time.January,
		"february": time.February, "feb": time.February,
		"march": time.March, "mar": time.March,
		"april": time.April, "apr": time.April,
		"may":  time.May,
		"june": time.June, "jun": time.June,
		"july": time.July, "jul": time.July,
		"august": time.August, "aug": time.August,
		"september": time.September, "sep": time.September, "sept": time.September,
		"october": time.October, "oct": time.October,
		"november": time.November, "nov": time.November,
		"december": time.December, "dec": time.December,
	}
	// "March 2, 2023"
	if m := enDate1RX.FindStringSubmatch(lb); len(m) == 4 {
		if mon := months[m[1]]; mon != 0 {
			var day, year int
			fmt.Sscanf(m[2], "%d", &day)
			fmt.Sscanf(m[3], "%d", &year)
			if day >= 1 && day <= 31 {
				return time.Date(year, mon, day, 0, 0, 0, 0, time.UTC), true
			}
		}
	}
	// "2 March 2023"
	if m := enDate2RX.FindStringSubmatch(lb); len(m) == 4 {
		if mon := months[m[2]]; mon != 0 {
			var day, year int
			fmt.Sscanf(m[1], "%d", &day)
			fmt.Sscanf(m[3], "%d", &year)
			if day >= 1 && day <= 31 {
				return time.Date(year, mon, day, 0, 0, 0, 0, time.UTC), true
			}
		}
	}
	return time.Time{}, false
}

func parseRuDate(lb string) (time.Time, bool) {
	if m := ruDateRX.FindStringSubmatch(lb); len(m) == 4 {
		mon := ruMonth[m[2]]
		if mon != 0 {
			var day, year int
			fmt.Sscanf(m[1], "%d", &day)
			fmt.Sscanf(m[3], "%d", &year)
			if day >= 1 && day <= 31 {
				return time.Date(year, mon, day, 0, 0, 0, 0, time.UTC), true
			}
		}
	}
	return time.Time{}, false
}

// ====================== Persistence ======================

func (c *Crawler) initResultFile() error {
	rf, err := os.OpenFile(c.cfg.FindingsPath, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		return err
	}
	tf, err := os.OpenFile(c.cfg.TargetsPath, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		rf.Close()
		return err
	}
	c.resF = rf
	c.resBw = bufio.NewWriterSize(rf, 1<<20)
	c.tgtF = tf
	c.tgtBw = bufio.NewWriterSize(tf, 1<<20)
	return nil
}

func (c *Crawler) closeResultFile() {
	if c.resBw != nil {
		_ = c.resBw.Flush()
	}
	if c.tgtBw != nil {
		_ = c.tgtBw.Flush()
	}
	if c.resF != nil {
		_ = c.resF.Close()
	}
	if c.tgtF != nil {
		_ = c.tgtF.Close()
	}
}

func (c *Crawler) writeFindings(ff []*Finding) {
	c.resultMu.Lock()
	defer c.resultMu.Unlock()

	for _, f := range ff {
		// write JSONL
		b, _ := json.Marshal(f)
		c.resBw.Write(b)
		c.resBw.WriteByte('\n')

		// write target page URL (not action), unique
		key := f.URL
		if _, loaded := c.targets.LoadOrStore(key, struct{}{}); !loaded {
			c.tgtBw.WriteString(key)
			c.tgtBw.WriteByte('\n')
			atomic.AddInt64(&c.targetsCount, 1)
		}
	}
	// Флушим только каждые 10 записей или в конце
	if len(ff) >= 10 || len(ff) > 0 {
		_ = c.resBw.Flush()
		_ = c.tgtBw.Flush()
	}
}

func (c *Crawler) writeAntibot(domain, reason string) {
	c.resultMu.Lock()
	defer c.resultMu.Unlock()
	af, err := os.OpenFile(c.cfg.AntibotPath, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		return
	}
	defer af.Close()
	rec := map[string]string{
		"domain": domain,
		"reason": reason,
		"ts":     time.Now().UTC().Format(time.RFC3339),
	}
	j, _ := json.Marshal(rec)
	af.Write(j)
	af.Write([]byte("\n"))
}

func (c *Crawler) loadCheckpoint() *Checkpoint {
	f, err := os.Open(c.cfg.CheckpointPath)
	if err != nil {
		return &Checkpoint{Processed: make(map[string]bool), Pos: 0}
	}
	defer f.Close()
	var cp Checkpoint
	if err := json.NewDecoder(f).Decode(&cp); err != nil {
		return &Checkpoint{Processed: make(map[string]bool), Pos: 0}
	}
	if cp.Processed == nil {
		cp.Processed = make(map[string]bool)
	}
	return &cp
}

func (c *Crawler) saveCheckpoint(pos int) {
	c.ckMu.Lock()
	defer c.ckMu.Unlock()
	if c.checkpoint == nil {
		return
	}
	tmp := *c.checkpoint
	tmp.Pos = pos

	f, err := os.CreateTemp("", "checkpoint-*.json")
	if err != nil {
		return
	}
	enc := json.NewEncoder(f)
	enc.SetIndent("", "  ")
	if err := enc.Encode(&tmp); err != nil {
		f.Close()
		return
	}
	f.Close()
	_ = os.Rename(f.Name(), c.cfg.CheckpointPath)
}

// ====================== Stats / Logs ======================

func (c *Crawler) printStats() {
	var ms runtime.MemStats
	runtime.ReadMemStats(&ms)
	reqs := atomic.LoadInt64(&c.client.requests)
	readMB := float64(atomic.LoadInt64(&c.client.bytesRead)) / (1024 * 1024)

	log.Printf("Progress: %d domains, %d forms, %d errors in %s | Memory: %dMB | Goroutines: %d | Net: %.1f MB read | Req: %d",
		atomic.LoadInt64(&c.processedDomains),
		atomic.LoadInt64(&c.foundForms),
		atomic.LoadInt64(&c.errorsCount),
		time.Since(c.startTime).Truncate(time.Second),
		ms.Alloc/(1024*1024),
		runtime.NumGoroutine(),
		readMB, reqs)
}

func (c *Crawler) printFinalStats() {
	elapsed := time.Since(c.startTime)
	reqs := atomic.LoadInt64(&c.client.requests)
	readMB := float64(atomic.LoadInt64(&c.client.bytesRead)) / (1024 * 1024)

	log.Printf("Completed in %s: domains=%d, forms_saved=%d, targets=%d, errors=%d | NetRead=%.1f MB, Requests=%d, SystemErrorPages=%d",
		elapsed.Truncate(time.Millisecond),
		atomic.LoadInt64(&c.processedDomains),
		atomic.LoadInt64(&c.foundForms),
		atomic.LoadInt64(&c.targetsCount),
		atomic.LoadInt64(&c.errorsCount),
		readMB, reqs, atomic.LoadInt64(&c.sysErrPages))

	// error kinds
	type kv struct {
		k string
		v int64
	}
	var kinds []kv
	c.errorKinds.Range(func(k, v any) bool {
		kinds = append(kinds, kv{k: k.(string), v: atomic.LoadInt64(v.(*int64))})
		return true
	})
	if len(kinds) > 0 {
		sort.Slice(kinds, func(i, j int) bool { return kinds[i].v > kinds[j].v })
		var b strings.Builder
		for i, kvp := range kinds {
			if i > 0 {
				b.WriteString(", ")
			}
			fmt.Fprintf(&b, "%s=%d", kvp.k, kvp.v)
		}
		log.Printf("Errors by kind: %s", b.String())
	}
	if c.contactsSkipped > 0 || c.authSkipped > 0 {
		log.Printf("Skipped: contacts=%d, auth=%d", c.contactsSkipped, c.authSkipped)
	}
}

// ====================== Utils ======================

func normalizeDomainLine(line string) string {
	line = strings.TrimSpace(line)
	line = strings.TrimPrefix(line, "http://")
	line = strings.TrimPrefix(line, "https://")
	line = strings.TrimPrefix(line, "www.")
	if i := strings.IndexAny(line, "/?#"); i >= 0 {
		line = line[:i]
	}
	return strings.ToLower(line)
}

func dedupStrings(in []string) []string {
	if len(in) == 0 {
		return in
	}
	m := make(map[string]struct{}, len(in))
	out := make([]string, 0, len(in))
	for _, s := range in {
		if _, ok := m[s]; ok {
			continue
		}
		m[s] = struct{}{}
		out = append(out, s)
	}
	return out
}

func attrValues(sel *goquery.Selection, attr string) []string {
	var out []string
	sel.Find("input, textarea, button, label").Each(func(_ int, el *goquery.Selection) {
		if v, ok := el.Attr(attr); ok {
			out = append(out, v)
		}
	})
	return out
}

func attrOr(sel *goquery.Selection, name, def string) string {
	if v, ok := sel.Attr(name); ok {
		return v
	}
	return def
}

func extractDomain(rawURL string) string {
	u, err := url.Parse(rawURL)
	if err != nil {
		return ""
	}
	return strings.ToLower(u.Hostname())
}

func resolveAction(pageURL, action string) string {
	if action == "" {
		return ""
	}
	pu, err := url.Parse(pageURL)
	if err != nil {
		return action
	}
	a, err := url.Parse(action)
	if err != nil {
		return action
	}
	res := pu.ResolveReference(a)
	res.Fragment = ""
	return res.String()
}

// ====================== Dedup (64-bit hash) ======================

type FormTracker struct {
	m sync.Map // map[uint64]struct{}
}

func (t *FormTracker) Add(h uint64) bool {
	_, loaded := t.m.LoadOrStore(h, struct{}{})
	return !loaded
}

func (c *Crawler) generateFindingHash(f *Finding) uint64 {
	key := f.Domain + "|" + f.URL + "|" + f.Classification + "|" + f.FormActionResolved + "|" + f.ContentDateISO
	h := fnv.New64a()
	_, _ = h.Write([]byte(key))
	return h.Sum64()
}

func writeLines(path string, lines []string) error {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()
	w := bufio.NewWriter(f)
	for _, l := range lines {
		if _, err := w.WriteString(l + "\n"); err != nil {
			return err
		}
	}
	return w.Flush()
}

func mergeCookies(existing []*http.Cookie, incoming []*http.Cookie) []*http.Cookie {
	now := time.Now()
	m := make(map[string]*http.Cookie, len(existing)+len(incoming))
	for _, c := range existing {
		if c.Expires.IsZero() || c.Expires.After(now) {
			key := c.Name + "|" + c.Domain + "|" + c.Path
			m[key] = c
		}
	}
	for _, c := range incoming {
		if c.Expires.IsZero() || c.Expires.After(now) {
			key := c.Name + "|" + c.Domain + "|" + c.Path
			m[key] = c
		}
	}
	out := make([]*http.Cookie, 0, len(m))
	for _, c := range m {
		out = append(out, c)
	}
	return out
}
