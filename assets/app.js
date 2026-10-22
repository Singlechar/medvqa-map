/* ============================================================================
 * 研究文献映射库 · MedVQA
 * 零构建 / 零后端 / 无第三方依赖。双击 index.html（file://）或经静态服务器打开均可。
 * 数据源：data/papers.json（http 下 fetch）；data/papers.offline.js（file:// 离线兜底）。
 * 结构：常量与工具 → 状态 → 存储/URL → 数据装载 → 筛选排序 → 四个视图 → 抽屉
 *       → 导出 → 事件绑定 → 启动。
 * ============================================================================ */
(function () {
  'use strict';

  /* ------------------------------------------------------------------ 常量 */

  var LS_DRAFT = 'medvqa-papers-draft-v1';
  var LS_THEME = 'medvqa-theme-v1';
  var LS_READ_LABEL = 'medvqa-read-label-v1';
  var DATA_FILE = 'data/papers.json';

  var TIERS = ['T1', 'T2', 'T3'];
  var RCS = ['RC1', 'RC2', 'RC3', '背景'];
  var CAPS = ['拒答', '多轮追问', '校准', '归因', '幻觉', '融合', '知识', '数据集', '基准'];
  var DEPTHS = ['题名', '摘要', '略读', '精读'];
  var STATUSES = ['待读', '在读', '已读'];
  var TYPES = ['综述', '方法', '基准', '数据集', '立场'];

  /** 阅读状态（圆点）：由 depth/status 推导，不新增数据字段。 */
  var READ_STATES = ['未读', '在读', '略读', '精读'];
  var READ_CLASS = { '未读': 'unread', '在读': 'reading', '略读': 'skim', '精读': 'deep' };
  var READ_ORDER = { '未读': 0, '在读': 1, '略读': 2, '精读': 3 };

  var RC_FULL = {
    RC1: '可答性判断与风险标尺',
    RC2: '关键缺失证据归因与最小澄清',
    RC3: '证据链增量融合与风险稳定更新',
    '背景': '领域全景与背景文献'
  };
  var RC_CLASS = { RC1: 'rc1', RC2: 'rc2', RC3: 'rc3', '背景': 'bg' };
  var TIER_NOTE = { T1: '必读', T2: '相关', T3: '背景' };

  /** 允许在抽屉里编辑、并计入“未导出修改”的字段（与数据模型一一对应，不改字段名）。 */
  var EDIT_FIELDS = ['tier', 'rc', 'caps', 'depth', 'status', 'score',
    'one_liner', 'borrowable', 'gap', 'keywords', 'note', 'links', 'pdf'];

  var SORT_KEYS = ['year', 'score', 'venue', 'tier'];

  /* ------------------------------------------------------------ DOM / 工具 */

  function $(sel, root) { return (root || document).querySelector(sel); }
  function $$(sel, root) { return Array.prototype.slice.call((root || document).querySelectorAll(sel)); }

  function esc(v) {
    return String(v == null ? '' : v).replace(/[&<>"']/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c];
    });
  }

  function str(v) { return v == null ? '' : String(v).trim(); }

  /** 多值字段归一：数组直接用；字符串按 | ; ； , 切分。全部空值安全。 */
  function toArr(v) {
    if (Array.isArray(v)) {
      return v.map(function (x) { return str(x); }).filter(Boolean);
    }
    if (v == null) return [];
    if (typeof v === 'number') return [String(v)];
    if (typeof v === 'string') {
      return v.split(/[|;；,，]/).map(function (x) { return x.trim(); }).filter(Boolean);
    }
    return [];
  }

  function clone(o) { return JSON.parse(JSON.stringify(o)); }

  function debounce(fn, ms) {
    var t = null;
    return function () {
      var ctx = this, args = arguments;
      if (t) clearTimeout(t);
      t = setTimeout(function () { t = null; fn.apply(ctx, args); }, ms);
    };
  }

  function pad2(n) { return (n < 10 ? '0' : '') + n; }
  function todayISO() {
    var d = new Date();
    return d.getFullYear() + '-' + pad2(d.getMonth() + 1) + '-' + pad2(d.getDate());
  }

  /** 显示用：空值统一显示破折号。 */
  function dash(v) { var t = str(v); return t === '' ? '—' : esc(t); }

  function unionKeys(a, b) {
    var out = {}, k;
    for (k in a) if (Object.prototype.hasOwnProperty.call(a, k)) out[k] = 1;
    for (k in b) if (Object.prototype.hasOwnProperty.call(b, k)) out[k] = 1;
    return Object.keys(out);
  }

  /* ------------------------------------------------------------------ 状态 */

  var state = {
    view: 'list',
    q: '',
    filters: {
      tier: [], rc: [], depth: [], status: [], read: [],
      yearFrom: null, yearTo: null, venue: ''
    },
    groupTier: true,
    sort: { key: 'year', dir: 'desc' },
    matrixDim: 'rc',
    matrixT1: false,
    timelineGroup: 'rc',
    collapsed: {},
    openId: null,
    selectedId: null,         // 列表里最后点击/聚焦的行（Delete 键作用对象）
    readLabel: false,         // 列表圆点是否显示文字标签（存 localStorage）
    noteMode: 'write',        // write | preview
    theme: 'auto',
    dataSource: '',
    meta: { version: 1, updatedAt: '' },
    papers: [],               // 当前工作副本（含未导出修改）
    baseline: [],             // papers.json 原始快照
    baseOverrides: {},        // papers.json 里的 matrix_overrides
    overrides: {},            // 当前矩阵三态覆盖
    dirtyCount: 0
  };

  var lastHash = null;

  /* --------------------------------------------------------- 论文归一化 */

  function authorFrom(authors) {
    var first = str(authors).split(/[;,,]/)[0];
    return first;
  }

  function normalizePaper(raw, idx) {
    var p = (raw && typeof raw === 'object') ? raw : {};
    var links = (p.links && typeof p.links === 'object') ? p.links : {};

    var year = Number(p.year);
    var hasYear = !(p.year === null || p.year === undefined || p.year === '' || !isFinite(year));

    var score = Number(p.score);
    var hasScore = (p.score !== null && p.score !== undefined && p.score !== '' && isFinite(score));
    if (hasScore) score = Math.min(5, Math.max(1, Math.round(score)));

    var tier = str(p.tier);
    var depth = str(p.depth);
    var status = str(p.status);
    var rc = toArr(p.rc).filter(function (x) { return RCS.indexOf(x) >= 0; });
    var caps = toArr(p.caps).filter(function (x) { return CAPS.indexOf(x) >= 0; });

    return {
      id: str(p.id) || ('paper-' + (idx + 1)),
      title: str(p.title),
      title_zh: str(p.title_zh),
      authors: str(p.authors),
      first_author: str(p.first_author) || authorFrom(p.authors),
      year: hasYear ? Math.round(year) : null,
      venue: str(p.venue),
      type: str(p.type),
      tier: TIERS.indexOf(tier) >= 0 ? tier : '',
      rc: rc,
      caps: caps,
      depth: DEPTHS.indexOf(depth) >= 0 ? depth : '',
      status: STATUSES.indexOf(status) >= 0 ? status : '',
      score: hasScore ? score : null,
      one_liner: str(p.one_liner),
      borrowable: str(p.borrowable),
      gap: str(p.gap),
      keywords: toArr(p.keywords),
      links: { doi: str(links.doi), arxiv: str(links.arxiv), url: str(links.url) },
      pdf: str(p.pdf),
      note: str(p.note),
      added_at: str(p.added_at),
      updated_at: str(p.updated_at)
    };
  }

  function normalizeOverrides(raw) {
    var out = {};
    if (!raw || typeof raw !== 'object') return out;
    Object.keys(raw).forEach(function (k) {
      var v = raw[k];
      if (v === 0 || v === 1 || v === 2) out[k] = v;
    });
    return out;
  }

  /* --------------------------------------------------------- 阅读状态 / 链接 */

  /** 阅读状态：depth 优先于 status（精读 > 略读 > 在读 > 未读），不新增数据字段。 */
  function readingState(p) {
    if (!p) return '未读';
    if (p.depth === '精读') return '精读';
    if (p.depth === '略读') return '略读';
    if (p.status === '在读') return '在读';
    return '未读';
  }

  /** 排序用的派生值：未读 0 → 在读 1 → 略读 2 → 精读 3。 */
  function depthOrder(p) { return READ_ORDER[readingState(p)]; }

  function readTip(p) {
    return '阅读状态：' + readingState(p) +
      '（depth=' + (p && p.depth ? p.depth : '空') + ', status=' + (p && p.status ? p.status : '空') + '）';
  }

  /** 圆点 + 文字标签；标签默认只在列表且开关打开 / 打印时显示（CSS 控制）。四处共用。 */
  function readDotHtml(p) {
    var st = readingState(p);
    var tip = readTip(p);
    return '<span class="read-dot read-' + READ_CLASS[st] + '" title="' + esc(tip) +
      '" aria-label="' + esc(tip) + '"></span>' +
      '<span class="read-label read-label-' + READ_CLASS[st] + '">' + esc(st) + '</span>';
  }

  /** 获取地址推导：url > doi > arxiv；只在展示层派生，不改数据字段。 */
  function effectiveUrl(p) {
    if (!p) return '';
    var links = p.links || {};
    var url = str(links.url);
    if (url) return url;
    var doi = str(links.doi);
    if (doi) return 'https://doi.org/' + doi;
    var arxiv = str(links.arxiv);
    if (arxiv) return 'https://arxiv.org/abs/' + arxiv;
    return '';
  }

  function hasLink(p) { return !!effectiveUrl(p); }

  function readLabelPref() {
    try { return localStorage.getItem(LS_READ_LABEL) === '1'; } catch (e) { return false; }
  }

  function saveReadLabelPref(on) {
    try { localStorage.setItem(LS_READ_LABEL, on ? '1' : '0'); } catch (e) { /* 忽略 */ }
  }

  /* --------------------------------------------------------------- 草稿存储 */

  function readDraft() {
    try {
      var raw = localStorage.getItem(LS_DRAFT);
      if (!raw) return null;
      var d = JSON.parse(raw);
      if (!d || !Array.isArray(d.papers)) return null;
      return d;
    } catch (e) { return null; }
  }

  function saveDraftNow() {
    try {
      localStorage.setItem(LS_DRAFT, JSON.stringify({
        baseVersion: state.meta.version,
        baseUpdatedAt: state.meta.updatedAt,
        papers: state.papers,
        matrix_overrides: state.overrides,
        savedAt: new Date().toISOString()
      }));
    } catch (e) {
      toast('本地保存失败：' + (e && e.message ? e.message : e));
    }
  }

  var saveDraftSoon = debounce(saveDraftNow, 300);

  function clearDraft() {
    try { localStorage.removeItem(LS_DRAFT); } catch (e) { /* 忽略 */ }
  }

  /* --------------------------------------------------------------- URL hash */

  /** hash 是筛选/视图的唯一真源；刷新、复制链接都以它为准。 */
  function parseHash() {
    var f = state.filters;
    f.tier = []; f.rc = []; f.depth = []; f.status = []; f.read = [];
    f.yearFrom = null; f.yearTo = null; f.venue = '';
    state.q = '';
    state.view = 'list';
    state.groupTier = true;
    state.sort = { key: 'year', dir: 'desc' };
    state.matrixDim = 'rc';
    state.matrixT1 = false;
    state.timelineGroup = 'rc';

    var raw = String(location.hash || '').replace(/^#/, '');
    if (!raw) return;
    var hp;
    try { hp = new URLSearchParams(raw); } catch (e) { return; }

    var v = hp.get('v');
    if (['list', 'board', 'matrix', 'timeline'].indexOf(v) >= 0) state.view = v;
    if (hp.has('q')) state.q = hp.get('q') || '';

    function pick(name, vocab) {
      return (hp.get(name) || '').split(',').map(function (x) { return x.trim(); })
        .filter(function (x) { return x && (!vocab || vocab.indexOf(x) >= 0); });
    }
    f.tier = pick('tier', TIERS);
    f.rc = pick('rc', RCS);
    f.depth = pick('depth', DEPTHS);
    f.status = pick('status', STATUSES);
    f.read = pick('read', READ_STATES);

    var y0 = parseInt(hp.get('y0'), 10);
    var y1 = parseInt(hp.get('y1'), 10);
    if (isFinite(y0)) f.yearFrom = y0;
    if (isFinite(y1)) f.yearTo = y1;
    f.venue = hp.get('venue') || '';

    if (hp.get('g') === '0') state.groupTier = false;
    else if (hp.get('g') === '1') state.groupTier = true;

    var srt = (hp.get('s') || '').split(':');
    if (srt.length === 2 && SORT_KEYS.indexOf(srt[0]) >= 0 && ['asc', 'desc'].indexOf(srt[1]) >= 0) {
      state.sort = { key: srt[0], dir: srt[1] };
    }

    var c = hp.get('c');
    if (['rc', 'caps', 'venue'].indexOf(c) >= 0) state.matrixDim = c;
    if (hp.get('t1') === '1') state.matrixT1 = true;
    var tg = hp.get('tg');
    if (['rc', 'tier'].indexOf(tg) >= 0) state.timelineGroup = tg;
  }

  function buildHash() {
    var p = new URLSearchParams();
    var f = state.filters;
    if (state.view !== 'list') p.set('v', state.view);
    if (state.q.trim()) p.set('q', state.q.trim());
    if (f.tier.length) p.set('tier', f.tier.join(','));
    if (f.rc.length) p.set('rc', f.rc.join(','));
    if (f.depth.length) p.set('depth', f.depth.join(','));
    if (f.status.length) p.set('status', f.status.join(','));
    if (f.read.length) p.set('read', f.read.join(','));
    if (f.yearFrom != null) p.set('y0', String(f.yearFrom));
    if (f.yearTo != null) p.set('y1', String(f.yearTo));
    if (f.venue) p.set('venue', f.venue);
    if (!state.groupTier) p.set('g', '0');
    if (state.sort.key !== 'year' || state.sort.dir !== 'desc') p.set('s', state.sort.key + ':' + state.sort.dir);
    if (state.matrixDim !== 'rc') p.set('c', state.matrixDim);
    if (state.matrixT1) p.set('t1', '1');
    if (state.timelineGroup !== 'rc') p.set('tg', state.timelineGroup);
    var qs = p.toString();
    return qs ? '#' + qs : '#';
  }

  function syncHash() {
    var target = buildHash();
    if (target === lastHash) return;
    lastHash = target;
    try {
      history.replaceState(null, '', target);
    } catch (e) {
      // file:// 下个别环境不允许 replaceState，退化为同文档跳转（不刷新页面）
      try { if (location.hash !== target) location.replace(target); } catch (e2) { /* 忽略 */ }
    }
  }

  /* ------------------------------------------------------------- 数据装载 */

  /**
   * file:// 下浏览器禁止 fetch 本地 JSON（控制台会报 CORS 错），因此直接使用
   * data/papers.offline.js 注入的副本；http(s) 下优先 fetch papers.json，
   * 失败才回退副本。两条路径都不会在控制台产生错误。
   */
  async function loadData() {
    var offline = (typeof window !== 'undefined' && window.__PAPERS_OFFLINE__) || null;

    if (location.protocol === 'file:') {
      if (!offline) throw new Error('缺少 data/papers.offline.js 离线副本');
      return { json: offline, source: 'offline' };
    }

    try {
      var res = await fetch(DATA_FILE, { cache: 'no-store' });
      if (!res.ok) throw new Error('HTTP ' + res.status);
      return { json: await res.json(), source: 'json' };
    } catch (err) {
      if (offline) return { json: offline, source: 'offline-fallback' };
      throw err;
    }
  }

  function applyData(json) {
    var arr = (json && Array.isArray(json.papers)) ? json.papers : [];
    state.baseline = arr.map(normalizePaper);
    state.meta = {
      version: (json && json.version != null) ? json.version : 1,
      updatedAt: (json && json.updated_at) ? str(json.updated_at) : ''
    };
    state.baseOverrides = normalizeOverrides(json && json.matrix_overrides);
    state.papers = clone(state.baseline);
    state.overrides = clone(state.baseOverrides);
  }

  /* --------------------------------------------------------------- 差异统计 */

  function sig(v) {
    if (v === null || v === undefined) return '';
    if (Array.isArray(v)) {
      return JSON.stringify(v.map(function (x) { return str(x); }).sort());
    }
    if (typeof v === 'object') {
      var o = {};
      Object.keys(v).sort().forEach(function (k) {
        o[k] = (v[k] === null || v[k] === undefined) ? '' : str(v[k]);
      });
      return JSON.stringify(o);
    }
    return String(v);
  }

  function overridesDiffCount(a, b) {
    var n = 0;
    unionKeys(a, b).forEach(function (k) {
      var av = (a[k] === 0 || a[k] === 1 || a[k] === 2) ? a[k] : -1;
      var bv = (b[k] === 0 || b[k] === 1 || b[k] === 2) ? b[k] : -1;
      if (av !== bv) n += 1;
    });
    return n;
  }

  /**
   * 脏数据拆项：新增（papers 有 / baseline 无）+ 修改（字段差 + overrides 差）
   * + 删除（baseline 有 / papers 无）。删除也计入，修掉“删了不算脏”的 bug。
   */
  function dirtyBreakdown(papers, overrides, basePapers, baseOverrides) {
    var baseMap = new Map();
    var baseIds = [];
    (basePapers || []).forEach(function (b) { baseMap.set(b.id, b); baseIds.push(b.id); });
    var added = 0, modified = 0, removed = 0;
    var seen = {};
    (papers || []).forEach(function (p) {
      seen[p.id] = true;
      var b = baseMap.get(p.id);
      if (!b) { added += 1; return; }
      for (var i = 0; i < EDIT_FIELDS.length; i++) {
        if (sig(p[EDIT_FIELDS[i]]) !== sig(b[EDIT_FIELDS[i]])) modified += 1;
      }
    });
    baseIds.forEach(function (id) { if (!seen[id]) removed += 1; });
    modified += overridesDiffCount(overrides || {}, baseOverrides || {});
    return { added: added, modified: modified, removed: removed };
  }

  function diffCount(papers, overrides, basePapers, baseOverrides) {
    var d = dirtyBreakdown(papers, overrides, basePapers, baseOverrides);
    return d.added + d.modified + d.removed;
  }

  function computeDirtyCount() {
    state.dirtyBreakdown = dirtyBreakdown(state.papers, state.overrides, state.baseline, state.baseOverrides);
    return state.dirtyBreakdown.added + state.dirtyBreakdown.modified + state.dirtyBreakdown.removed;
  }

  /* --------------------------------------------------------- 筛选 / 排序 */

  function haystack(p) {
    return [
      p.title, p.title_zh, p.first_author, p.authors,
      p.one_liner, p.borrowable, p.gap,
      p.keywords.join(' '), p.note
    ].join(' \n ').toLowerCase();
  }

  function matches(p) {
    var f = state.filters;
    if (f.tier.length && f.tier.indexOf(p.tier) < 0) return false;
    if (f.rc.length && !f.rc.some(function (x) { return p.rc.indexOf(x) >= 0; })) return false;
    if (f.depth.length && f.depth.indexOf(p.depth) < 0) return false;
    if (f.status.length && f.status.indexOf(p.status) < 0) return false;
    if (f.read.length && f.read.indexOf(readingState(p)) < 0) return false;
    if (f.yearFrom != null && (p.year == null || p.year < f.yearFrom)) return false;
    if (f.yearTo != null && (p.year == null || p.year > f.yearTo)) return false;
    if (f.venue && p.venue !== f.venue) return false;

    var q = state.q.trim().toLowerCase();
    if (q) {
      var hay = haystack(p);
      var toks = q.split(/\s+/);
      for (var i = 0; i < toks.length; i++) {
        if (hay.indexOf(toks[i]) < 0) return false;
      }
    }
    return true;
  }

  function filtered() { return state.papers.filter(matches); }

  /** 空值一律排在最后（不随升降序翻转），组内再按年份降序。 */
  function cmpNullable(a, b, dir) {
    var an = (a === null || a === undefined || a === '');
    var bn = (b === null || b === undefined || b === '');
    if (an && bn) return 0;
    if (an) return 1;
    if (bn) return -1;
    if (a < b) return -1 * dir;
    if (a > b) return 1 * dir;
    return 0;
  }

  function isNewPaper(p) {
    if (!p) return false;
    for (var i = 0; i < state.baseline.length; i++) {
      if (state.baseline[i].id === p.id) return false;
    }
    return true;
  }

  function sortPapers(list) {
    var key = state.sort.key;
    var dir = state.sort.dir === 'asc' ? 1 : -1;
    var out = list.slice();

    out.sort(function (a, b) {
      // 本次新增（baseline 里没有）的条目始终置顶，刚添加的文献一眼可见
      var na = isNewPaper(a), nb = isNewPaper(b);
      if (na !== nb) return na ? -1 : 1;
      var r = 0;
      if (key === 'year') r = cmpNullable(a.year, b.year, dir);
      else if (key === 'score') r = cmpNullable(a.score, b.score, dir);
      else if (key === 'tier') {
        var ai = TIERS.indexOf(a.tier), bi = TIERS.indexOf(b.tier);
        r = cmpNullable(ai < 0 ? null : ai, bi < 0 ? null : bi, dir);
      } else if (key === 'venue') {
        r = cmpNullable(str(a.venue) || null, str(b.venue) || null, dir);
      }
      if (r === 0) r = cmpNullable(a.year, b.year, 1); // 同年按年份兜底（稳定）
      if (r === 0) r = str(a.title).localeCompare(str(b.title));
      return r;
    });
    return out;
  }

  /* --------------------------------------------------------------- 渲染主控 */

  function render() {
    var list = filtered();
    $('#hit-n').textContent = String(list.length);
    $('#total-n').textContent = String(state.papers.length);
    $('#search-clear').hidden = !state.q;

    renderDirty();
    syncControls();
    renderView(list);
    renderSourceNote();
    syncHash();
  }

  function renderDirty() {
    var el = $('#dirty-badge');
    if (state.dirtyCount > 0) {
      var d = state.dirtyBreakdown || { added: 0, modified: 0, removed: 0 };
      el.hidden = false;
      el.textContent = '有 ' + state.dirtyCount + ' 处未导出的修改';
      el.title = '新增 ' + d.added + ' · 修改 ' + d.modified + ' · 删除 ' + d.removed +
        '\n修改已自动存到浏览器 localStorage；点击「导出」下载 papers.json 才算真正落盘。';
    } else {
      el.hidden = true;
      el.textContent = '';
      el.title = '';
    }
  }

  function renderSourceNote() {
    var el = $('#source-note');
    if (!el) return;
    var txt, tip;
    if (state.dataSource === 'json') {
      txt = '数据源：data/papers.json';
      tip = '通过 fetch 读取 papers.json（版本 ' + state.meta.version + '，更新于 ' + (state.meta.updatedAt || '未知') + '）';
    } else if (state.dataSource === 'offline') {
      txt = '数据源：内嵌离线副本';
      tip = '当前以 file:// 打开，浏览器不允许读取本地 papers.json，已使用 data/papers.offline.js。' +
        '修改 papers.json 后，请用「导出 → 导出离线副本」或 node tools/sync-offline.mjs 同步。';
    } else {
      txt = '数据源：离线副本（papers.json 读取失败）';
      tip = 'fetch data/papers.json 失败，已回退到内嵌副本。若用本地服务器打开，请确认 data/papers.json 存在。';
    }
    el.textContent = txt;
    el.title = tip;
  }

  /** 把 state 同步回静态控件（筛选 chip、年份输入、开关、分段按钮）。 */
  function syncControls() {
    var f = state.filters;
    $$('.chip-row[data-filter]').forEach(function (row) {
      var name = row.getAttribute('data-filter');
      var values = f[name] || [];
      $$('.chip', row).forEach(function (chip) {
        var v = chip.getAttribute('data-value');
        chip.classList.toggle('is-on', values.indexOf(v) >= 0);
        chip.setAttribute('aria-pressed', values.indexOf(v) >= 0 ? 'true' : 'false');
      });
    });

    var yf = $('#year-from'), yt = $('#year-to');
    if (yf && document.activeElement !== yf) yf.value = f.yearFrom == null ? '' : String(f.yearFrom);
    if (yt && document.activeElement !== yt) yt.value = f.yearTo == null ? '' : String(f.yearTo);

    var vs = $('#venue-select');
    if (vs) vs.value = f.venue;

    var gt = $('#group-toggle');
    if (gt) gt.checked = state.groupTier;

    var rlt = $('#read-label-toggle');
    if (rlt) rlt.checked = state.readLabel;

    var mt1 = $('#matrix-t1');
    if (mt1) mt1.checked = state.matrixT1;

    $$('#viewtabs .viewtab').forEach(function (b) {
      b.classList.toggle('is-on', b.getAttribute('data-view') === state.view);
    });
    $$('#matrix-dim .seg-btn').forEach(function (b) {
      b.classList.toggle('is-on', b.getAttribute('data-dim') === state.matrixDim);
    });
    $$('#timeline-group .seg-btn').forEach(function (b) {
      b.classList.toggle('is-on', b.getAttribute('data-group') === state.timelineGroup);
    });
  }

  function renderView(list) {
    $$('.view').forEach(function (sec) {
      sec.hidden = sec.getAttribute('data-view') !== state.view;
    });
    var l = list || filtered();

    if (state.view === 'list') renderList(l);
    else if (state.view === 'board') renderBoard(l);
    else if (state.view === 'matrix') renderMatrix(l);
    else if (state.view === 'timeline') renderTimeline(l);
  }

  function emptyBlock(title, sub) {
    return '<div class="empty">' +
      '<div class="empty-title">' + esc(title) + '</div>' +
      '<div class="empty-sub">' + esc(sub || '') + '</div>' +
      '<div class="btn-row"><button type="button" class="btn" data-act="clear-filters">清空筛选</button>' +
      '<button type="button" class="btn" data-act="clear-search">清空搜索</button></div>' +
      '</div>';
  }

  /* ------------------------------------------------------------- 视图：列表 */

  var LIST_COLS = [
    { key: 'read', label: '·', w: '22px', sortable: false, cls: 'cell-read' },
    { key: 'tier', label: 'Tier', w: '44px', sortable: true, cls: 'is-center' },
    { key: 'year', label: '年份', w: '52px', sortable: true, cls: 'is-center' },
    { key: 'title', label: '标题 / 中文译名', w: '32%', sortable: false, cls: 'cell-title' },
    { key: 'venue', label: 'Venue', w: '138px', sortable: true, cls: 'is-clip' },
    { key: 'rc', label: 'RC', w: '128px', sortable: false, cls: 'cell-rc' },
    { key: 'depth', label: '深度', w: '52px', sortable: false, cls: 'cell-depth is-center' },
    { key: 'score', label: '相关', w: '58px', sortable: true, cls: 'is-center' },
    { key: 'one_liner', label: '一句话', w: 'auto', sortable: false, cls: 'cell-one' },
    { key: 'del', label: '', w: '28px', sortable: false, cls: 'cell-del' }
  ];

  /** 列表中文译名行尾的 ↗：只有存在有效获取地址时才渲染，不占位。 */
  function linkMark(p) {
    if (!hasLink(p)) return '';
    var url = effectiveUrl(p);
    return ' <a class="title-link" href="' + esc(url) + '" target="_blank" rel="noopener noreferrer"' +
      ' title="打开获取地址：' + esc(url) + '">↗</a>';
  }

  function rcChips(rc) {
    if (!rc || !rc.length) return '<span class="dash">—</span>';
    return '<span class="rc-chips">' + rc.map(function (x) {
      return '<span class="chip rc-chip ' + (RC_CLASS[x] || 'bg') + '">' + esc(x) + '</span>';
    }).join('') + '</span>';
  }

  function tierPill(tier) {
    if (!tier) return '<span class="dash">—</span>';
    return '<span class="tier-pill ' + esc(tier) + '" title="' + esc(tier + ' ' + (TIER_NOTE[tier] || '')) + '">' + esc(tier) + '</span>';
  }

  function scoreCell(score) {
    if (score == null) return '<span class="dash">—</span>';
    var pct = Math.round((score / 5) * 100);
    return '<span class="score-value">' + score + '</span>' +
      '<span class="score-bar"><i style="width:' + pct + '%"></i></span>';
  }

  function listHeadHtml() {
    var cells = LIST_COLS.map(function (col) {
      var sorted = state.sort.key === col.key;
      var arrow = '';
      if (sorted) arrow = '<span class="sort-arrow">' + (state.sort.dir === 'asc' ? '▲' : '▼') + '</span>';
      if (col.sortable) {
        return '<th scope="col" data-sort="' + col.key + '" class="sortable' +
          (sorted ? ' is-sorted' : '') + ' ' + col.cls + '">' + esc(col.label) + arrow + '</th>';
      }
      return '<th scope="col" class="' + col.cls + '">' + esc(col.label) + '</th>';
    }).join('');
    return '<thead><tr>' + cells + '</tr></thead>';
  }

  function listColgroupHtml() {
    var wideRead = !!state.readLabel;
    var cols = LIST_COLS.map(function (col) {
      var w = col.w;
      if (col.key === 'read') w = wideRead ? '74px' : '22px';
      else if (col.key === 'title') w = wideRead ? '30%' : '32%';
      return '<col style="width:' + (w === 'auto' ? 'auto' : w) + '">';
    }).join('');
    return '<colgroup>' + cols + '</colgroup>';
  }

  function listRowHtml(p) {
    var active = state.selectedId === p.id ? ' is-active' : '';
    return '<tr class="row' + active + '" data-id="' + esc(p.id) + '">' +
      '<td class="cell-read">' + readDotHtml(p) + '</td>' +
      '<td class="is-center">' + tierPill(p.tier) + '</td>' +
      '<td class="cell-year is-center">' + (p.year == null ? '—' : esc(p.year)) + '</td>' +
      '<td class="cell-title">' +
      '<div class="title-en" title="' + esc(p.title) + '">' + dash(p.title) + '</div>' +
      '<div class="title-zh" title="' + esc(p.title_zh) + '">' + dash(p.title_zh) + linkMark(p) + '</div>' +
      '</td>' +
      '<td class="cell-venue is-clip" title="' + esc(p.venue) + '">' + dash(p.venue) + '</td>' +
      '<td class="cell-rc">' + rcChips(p.rc) + '</td>' +
      '<td class="cell-depth is-center">' + dash(p.depth) + '</td>' +
      '<td class="cell-score is-center">' + scoreCell(p.score) + '</td>' +
      '<td class="cell-one" title="' + esc(p.one_liner) + '">' + dash(p.one_liner) + '</td>' +
      '<td class="cell-del"><button type="button" class="row-del" data-del="' + esc(p.id) +
      '" title="删除这篇（8 秒内可撤销）" aria-label="删除 ' + esc(p.title || p.id) + '">×</button></td>' +
      '</tr>';
  }

  function renderList(list) {
    var host = $('#list-host');
    var note = $('#list-note');
    var dirText = state.sort.dir === 'asc' ? '↑' : '↓';
    var keyText = { year: '年份', score: '相关度', venue: 'Venue', tier: 'Tier' }[state.sort.key] || state.sort.key;
    if (note) note.textContent = '共 ' + list.length + ' 篇 · 排序：' + keyText + ' ' + dirText;

    if (!list.length) {
      host.innerHTML = emptyBlock('没有命中的文献', '当前搜索与筛选条件相互叠加（AND），试试减少条件。');
      return;
    }

    var rows = sortPapers(list);

    if (!state.groupTier) {
      host.innerHTML = '<table class="list-table">' + listColgroupHtml() + listHeadHtml() +
        '<tbody>' + rows.map(listRowHtml).join('') + '</tbody></table>';
      return;
    }

    // 分组模式：T1 / T2 / T3 / 未标注（未标注仅在存在时出现）
    var groups = [];
    TIERS.forEach(function (t) {
      var items = rows.filter(function (p) { return p.tier === t; });
      if (items.length) groups.push({ key: t, label: t, items: items });
    });
    var untagged = rows.filter(function (p) { return TIERS.indexOf(p.tier) < 0; });
    if (untagged.length) groups.push({ key: '未标注', label: '未标注 tier', items: untagged });

    host.innerHTML = groups.map(function (g) {
      var collapsed = !!state.collapsed[g.key];
      var head = '<div class="tier-group-head" data-group="' + esc(g.key) + '" role="button" tabindex="0" ' +
        'aria-expanded="' + (collapsed ? 'false' : 'true') + '">' +
        (collapsed ? '▸' : '▾') + ' ' +
        (g.key === '未标注' ? esc(g.label) : tierPill(g.key) + ' ' + esc(TIER_NOTE[g.key] || '')) +
        ' <span class="tier-count">' + g.items.length + ' 篇</span></div>';
      var body = '<div class="tier-group-body">' +
        '<table class="list-table">' + listColgroupHtml() + listHeadHtml() +
        '<tbody>' + g.items.map(listRowHtml).join('') + '</tbody></table></div>';
      return '<section class="tier-group' + (collapsed ? ' collapsed' : '') + '" data-group="' + esc(g.key) + '">' +
        head + body + '</section>';
    }).join('');
  }

  /* ------------------------------------------------------------- 视图：看板 */

  function boardCardHtml(p) {
    return '<div class="card" draggable="true" data-id="' + esc(p.id) + '" tabindex="0">' +
      '<div class="card-title-row">' + readDotHtml(p) +
      '<div class="card-title" title="' + esc(p.title) + '">' + dash(p.title) + '</div>' +
      (hasLink(p) ? '<a class="card-link" href="' + esc(effectiveUrl(p)) + '" target="_blank" rel="noopener noreferrer"' +
        ' title="打开获取地址：' + esc(effectiveUrl(p)) + '">↗</a>' : '') +
      '</div>' +
      '<div class="card-title-zh" title="' + esc(p.title_zh) + '">' + dash(p.title_zh) + '</div>' +
      '<div class="card-meta">' + tierPill(p.tier) +
      ' <span class="card-year">' + (p.year == null ? '—' : esc(p.year)) + '</span>' +
      (p.venue ? ' · <span class="card-venue">' + esc(p.venue) + '</span>' : '') +
      '</div>' +
      '<div class="card-chips">' + rcChips(p.rc) + '</div>' +
      '</div>';
  }

  function renderBoard(list) {
    var host = $('#board-host');
    var cols = DEPTHS.slice();
    var buckets = {};
    cols.forEach(function (d) { buckets[d] = []; });
    var unset = [];
    list.forEach(function (p) {
      if (buckets[p.depth]) buckets[p.depth].push(p);
      else unset.push(p);
    });
    var allCols = cols.slice();
    if (unset.length) allCols.push('未标注');

    host.innerHTML = allCols.map(function (d) {
      var items = d === '未标注' ? unset : buckets[d];
      items = sortPapers(items);
      var cards = items.length
        ? items.map(boardCardHtml).join('')
        : '<div class="board-empty">拖到这里</div>';
      return '<section class="board-col" data-depth="' + esc(d) + '">' +
        '<div class="board-col-head">' + esc(d) + ' <span class="board-count">' + items.length + '</span></div>' +
        '<div class="board-cards" data-depth="' + esc(d) + '">' + cards + '</div>' +
        '</section>';
    }).join('');
  }

  /* ------------------------------------------------------------- 视图：矩阵 */

  var MATRIX_COL_W = { rc: 46, caps: 68, venue: 92 };

  function matrixColumns() {
    var dim = state.matrixDim;
    if (dim === 'rc') {
      return RCS.map(function (k) {
        return { key: k, label: k, sub: RC_FULL[k] || '', w: MATRIX_COL_W.rc };
      });
    }
    if (dim === 'caps') {
      return CAPS.map(function (k) {
        return { key: k, label: k, sub: '', w: MATRIX_COL_W.caps };
      });
    }
    // venue：按篇数降序，再按名称
    var counts = {};
    state.papers.forEach(function (p) {
      var v = str(p.venue);
      if (!v) return;
      counts[v] = (counts[v] || 0) + 1;
    });
    return Object.keys(counts).sort(function (a, b) {
      if (counts[b] !== counts[a]) return counts[b] - counts[a];
      return a.localeCompare(b);
    }).map(function (v) {
      return { key: v, label: v, sub: String(counts[v]) + ' 篇', w: MATRIX_COL_W.venue };
    });
  }

  function cellKey(id, dim, col) { return id + '|' + dim + '|' + col; }

  function derivedState(p, dim, col) {
    if (dim === 'rc') return p.rc.indexOf(col) >= 0 ? 2 : 0;
    if (dim === 'caps') return p.caps.indexOf(col) >= 0 ? 2 : 0;
    if (dim === 'venue') return p.venue === col ? 2 : 0;
    return 0;
  }

  function cellState(p, dim, col) {
    var ov = state.overrides[cellKey(p.id, dim, col)];
    if (ov === 0 || ov === 1 || ov === 2) return ov;
    return derivedState(p, dim, col);
  }

  function matrixRowOrder(list) {
    var rows = state.matrixT1 ? list.filter(function (p) { return p.tier === 'T1'; }) : list.slice();
    rows.sort(function (a, b) {
      var ai = TIERS.indexOf(a.tier), bi = TIERS.indexOf(b.tier);
      ai = ai < 0 ? 9 : ai; bi = bi < 0 ? 9 : bi;
      if (ai !== bi) return ai - bi;
      var ay = a.year == null ? -1 : a.year;
      var by = b.year == null ? -1 : b.year;
      if (ay !== by) return by - ay;
      return str(a.title).localeCompare(str(b.title));
    });
    return rows;
  }

  function shortName(p) {
    var a = p.first_author || '—';
    return a + (p.year == null ? '' : ' ' + p.year);
  }

  var ST_LABEL = { 2: '● 直接对应', 1: '◐ 部分相关', 0: '○ 不相关' };
  var ST_MARK = { 2: '●', 1: '◐', 0: '○' };

  function renderMatrix(list) {
    var host = $('#matrix-host');
    var cols = matrixColumns();
    var rows = matrixRowOrder(list);

    if (!cols.length || !rows.length) {
      host.innerHTML = emptyBlock('矩阵为空', state.matrixT1 ? '当前「只看 T1」+ 筛选条件下没有文献。' : '当前筛选条件下没有文献。');
      return;
    }

    var dim = state.matrixDim;

    // 列宽策略：rc / caps 用等分自适应（表格 100% 宽，铺满主区，截屏更像矩阵表）；
    // venue 列数不可控，用固定列宽并在 .matrix-scroll 内横向滚动。
    var fixedWidth = dim === 'venue';
    function colTag(c) {
      return fixedWidth ? '<col style="width:' + c.w + 'px">' : '<col>';
    }

    // 列计数：● 覆盖篇数、◐ 部分相关篇数
    var colCount = {};
    var colPart = {};
    cols.forEach(function (c) { colCount[c.key] = 0; colPart[c.key] = 0; });
    rows.forEach(function (p) {
      cols.forEach(function (c) {
        var st = cellState(p, dim, c.key);
        if (st === 2) colCount[c.key] += 1;
        else if (st === 1) colPart[c.key] += 1;
      });
    });

    var head = '<thead><tr>' +
      '<th scope="col" class="matrix-corner paper-col"><span class="matrix-corner-label">论文 \\ ' +
      (dim === 'rc' ? '研究内容' : dim === 'caps' ? '能力标签' : 'Venue') + '</span></th>' +
      cols.map(function (c) {
        return '<th scope="col" class="col-head" title="' + esc(c.sub || c.label) + '"' +
          (fixedWidth ? ' style="width:' + c.w + 'px"' : '') + '>' +
          '<span class="col-head-label">' + esc(c.label) + '</span>' +
          '<span class="col-count">' + colCount[c.key] + ' 篇 ●' +
          (colPart[c.key] ? ' · ' + colPart[c.key] + ' ◐' : '') + '</span></th>';
      }).join('') + '</tr></thead>';

    var body = '<tbody>' + rows.map(function (p) {
      var headTip = p.title + (hasLink(p) ? '\n获取地址：' + effectiveUrl(p) : '');
      return '<tr data-id="' + esc(p.id) + '">' +
        '<th scope="row" class="paper-col" title="' + esc(headTip) + '">' +
        '<span class="paper-read" title="' + esc(readTip(p)) + '">' + readDotHtml(p) + '</span>' +
        '<span class="paper-tier">' + esc(p.tier || '—') + '</span>' +
        '<span class="paper-name">' + esc(shortName(p)) + '</span>' +
        '</th>' +
        cols.map(function (c) {
          var st = cellState(p, dim, c.key);
          var tip = shortName(p) + ' × ' + c.label + '：' + ST_LABEL[st] + '（点击切换）' +
            (hasLink(p) ? '\n获取地址：' + effectiveUrl(p) : '');
          return '<td class="cell st-' + st + '" data-id="' + esc(p.id) + '" data-col="' + esc(c.key) +
            '" data-dim="' + esc(dim) + '" title="' + esc(tip) + '" role="button" tabindex="-1" ' +
            'aria-label="' + esc(tip) + '"><span class="cell-dot">' + ST_MARK[st] + '</span></td>';
        }).join('') +
        '</tr>';
    }).join('') + '</tbody>';

    var note = '<div class="matrix-note">' +
      '行按 T1→T3、年份降序 · 共 ' + rows.length + ' 篇 · 列 ' + cols.length + ' 个 · ' +
      '点击单元格循环：●→◐→○ · 改动计入“未导出修改”' +
      (state.matrixT1 ? ' · <b>当前只看 T1</b>' : '') +
      '</div>';

    host.innerHTML = '<div class="matrix-scroll"><table class="matrix-table">' +
      '<colgroup><col style="width:220px">' +
      cols.map(colTag).join('') +
      '</colgroup>' + head + body + '</table></div>' + note;
  }

  /* ----------------------------------------------------------- 视图：时间线 */

  function timelineGroups() {
    if (state.timelineGroup === 'tier') {
      return TIERS.map(function (t) {
        return { key: t, label: t + ' ' + (TIER_NOTE[t] || '') };
      });
    }
    // 纵轴标签只放 RC1/RC2/RC3/背景，完整释义放在图注里，避免 1366 下左侧被裁
    return RCS.map(function (k) { return { key: k, label: k }; });
  }

  function tierClassOf(p) {
    return p.tier === 'T1' ? 't1' : p.tier === 'T2' ? 't2' : p.tier === 'T3' ? 't3' : 't3';
  }

  function renderTimeline(list) {
    var host = $('#timeline-host');
    var legend = $('#timeline-legend');

    var points = [];
    list.forEach(function (p) {
      if (p.year == null) return;
      var gs;
      if (state.timelineGroup === 'tier') {
        gs = p.tier ? [p.tier] : [''];
      } else {
        gs = p.rc.length ? p.rc : [''];
      }
      gs.forEach(function (g) { points.push({ p: p, g: g }); });
    });

    // 图例：tier 三色 + 篇数
    var counts = { T1: 0, T2: 0, T3: 0, '': 0 };
    list.forEach(function (p) { counts[p.tier || ''] = (counts[p.tier || ''] || 0) + 1; });
    if (legend) {
      legend.innerHTML = ['T1', 'T2', 'T3'].map(function (t) {
        return '<span class="tl-legend-item"><i class="tl-swatch ' + t.toLowerCase() + '"></i>' +
          esc(t + ' ' + (TIER_NOTE[t] || '')) + ' <b>' + (counts[t] || 0) + '</b></span>';
      }).join('');
    }

    if (!points.length) {
      host.innerHTML = emptyBlock('没有可绘制的年份', '文献缺少 year 字段，或当前筛选结果为空。');
      return;
    }

    var groups = timelineGroups().filter(function (g) {
      return points.some(function (pt) { return pt.g === g.key; });
    });
    var hasUnset = points.some(function (pt) { return pt.g === ''; });
    if (hasUnset) groups.push({ key: '', label: '未标注' });

    var W = Math.max(640, host.clientWidth || 900);
    // 底部有 note 行，SVG 高度要减去它，否则 viewBox 会被 flex 压缩约 4%
    var H = Math.max(300, (host.clientHeight || 450) - 30);
    var padL = 104, padR = 20, padT = 16, padB = 38;
    var plotW = Math.max(80, W - padL - padR);
    var plotH = Math.max(80, H - padT - padB);

    var years = points.map(function (pt) { return pt.p.year; });
    var minY = Math.min.apply(null, years);
    var maxY = Math.max.apply(null, years);
    var span = Math.max(0, maxY - minY);

    function xOf(y) {
      if (span === 0) return padL + plotW / 2;
      return padL + ((y - minY) / span) * plotW;
    }

    var laneH = plotH / Math.max(1, groups.length);

    var parts = [];
    parts.push('<svg class="tl-svg" viewBox="0 0 ' + W + ' ' + H + '" width="' + W + '" height="' + H +
      '" role="img" aria-label="文献年份分布时间线">');

    // 分组背景带与标签
    groups.forEach(function (g, gi) {
      var top = padT + gi * laneH;
      var mid = top + laneH / 2;
      if (gi % 2 === 1) {
        parts.push('<rect class="tl-group-bg" x="' + padL + '" y="' + top + '" width="' + plotW +
          '" height="' + laneH + '"></rect>');
      }
      parts.push('<line class="tl-grid-line" x1="' + padL + '" y1="' + (top + laneH) + '" x2="' +
        (padL + plotW) + '" y2="' + (top + laneH) + '"></line>');
      parts.push('<text class="tl-group-label" x="' + (padL - 10) + '" y="' + (mid + 3.5) +
        '" text-anchor="end">' + esc(g.label) + '</text>');
    });

    // 年份刻度
    var step = 1;
    if (span > 12) step = 2;
    if (span > 24) step = 5;
    if (span > 60) step = 10;
    var tickStart = Math.ceil(minY / step) * step;
    for (var y = tickStart; y <= maxY; y += step) {
      var x = xOf(y);
      parts.push('<line class="tl-grid-line" x1="' + x.toFixed(1) + '" y1="' + padT + '" x2="' + x.toFixed(1) +
        '" y2="' + (padT + plotH) + '"></line>');
      parts.push('<text class="tl-year-label" x="' + x.toFixed(1) + '" y="' + (padT + plotH + 20) +
        '" text-anchor="middle">' + y + '</text>');
    }
    parts.push('<line class="tl-axis-line" x1="' + padL + '" y1="' + (padT + plotH) + '" x2="' +
      (padL + plotW) + '" y2="' + (padT + plotH) + '"></line>');

    // 点：同一分组同一年份内轻微抖动，避免完全重叠
    var buckets = {};
    groups.forEach(function (g) { buckets[g.key] = {}; });
    points.forEach(function (pt) {
      if (!buckets[pt.g]) buckets[pt.g] = {};
      var k = String(pt.p.year);
      if (!buckets[pt.g][k]) buckets[pt.g][k] = [];
      buckets[pt.g][k].push(pt.p);
    });

    groups.forEach(function (g, gi) {
      var top = padT + gi * laneH;
      var mid = top + laneH / 2;
      var byYear = buckets[g.key] || {};
      Object.keys(byYear).forEach(function (yearKey) {
        var arr = byYear[yearKey];
        var n = arr.length;
        var maxOff = Math.max(0, laneH / 2 - 9);
        var gap = Math.min(7, n > 1 ? (maxOff * 2) / (n - 1) : 0);
        arr.forEach(function (p, i) {
          var off = (i - (n - 1) / 2) * gap;
          if (off > maxOff) off = maxOff;
          if (off < -maxOff) off = -maxOff;
          var cx = xOf(p.year);
          var cy = mid + off;
          parts.push('<circle class="tl-dot ' + tierClassOf(p) + '" cx="' + cx.toFixed(1) + '" cy="' + cy.toFixed(1) +
            '" r="4.5" data-id="' + esc(p.id) + '" data-tip-title="' + esc(p.title) + '"' +
            ' data-tip-sub="' + esc((p.title_zh ? p.title_zh + ' · ' : '') + (p.one_liner || '')) + '"></circle>');
        });
      });
    });

    parts.push('</svg>');

    var warn = '';
    var noYear = list.length - list.filter(function (p) { return p.year != null; }).length;
    if (noYear > 0) warn = ' <span class="hint">（' + noYear + ' 篇缺少年份未绘制）</span>';

    host.innerHTML = parts.join('') + '<div class="timeline-note">横轴＝年份（' + minY + '–' + maxY +
      '）· 纵轴＝' + (state.timelineGroup === 'tier' ? 'tier' : '研究内容') +
      ' · 一点＝一篇（多 RC 文献会在多行重复出现）· 悬停看标题与一句话' + warn + '</div>';
  }

  /* --------------------------------------------------------------- 抽屉渲染 */

  function getPaper(id) {
    if (!id) return null;
    for (var i = 0; i < state.papers.length; i++) {
      if (state.papers[i].id === id) return state.papers[i];
    }
    return null;
  }

  /* --------------------------------------------------------- 获取地址编辑区 */

  var LINK_LABEL = { doi: 'DOI', arxiv: 'arXiv ID', url: '通用链接', pdf: '本地 PDF' };

  function linkValue(p, field) {
    if (field === 'pdf') return str(p.pdf);
    return str((p.links || {})[field]);
  }

  function linkHref(p, field) {
    var v = linkValue(p, field);
    if (!v) return '';
    if (field === 'doi') return 'https://doi.org/' + v;
    if (field === 'arxiv') return 'https://arxiv.org/abs/' + v;
    return v;
  }

  /**
   * 站内相对路径的线上解析：仓库根 = 站点根，所以线上（http/https）要把
   * "../02_参考文献/xxx.pdf" 开头的 "../" 去掉；本机双击（file://）保持原样，
   * 才能从 07_文献映射库/ 找到项目根目录的 02_参考文献/。
   * 已有协议（http/https/data/file…）的绝对地址一律原样返回。
   */
  function webSafePath(v) {
    var s = str(v);
    if (!s || /^[a-z][a-z0-9+.-]*:/i.test(s)) return s;
    if (location.protocol === 'file:') return s;
    while (/^\.\.\//.test(s)) s = s.slice(3);
    return s;
  }

  /** 失焦清洗：去首尾空格、URL 补协议、DOI 剥 doi.org 前缀、arXiv 剥 abs/pdf 前缀。 */
  function cleanLinkInput(field, raw) {
    var v = str(raw);
    if (!v) return '';
    if (field === 'doi') {
      v = v.replace(/^https?:\/\/(dx\.)?doi\.org\//i, '').replace(/^doi:\s*/i, '').trim();
    } else if (field === 'arxiv') {
      v = v.replace(/^https?:\/\/arxiv\.org\/(abs|pdf)\//i, '').replace(/\.pdf$/i, '').trim();
    } else if (field === 'url') {
      if (!/^([a-z][a-z0-9+.-]*:|\/|\.{1,2}\/)/i.test(v)) v = 'https://' + v;
    }
    return v;
  }

  function setLinkValue(p, field, value) {
    if (field === 'pdf') p.pdf = value;
    else p.links[field] = value;
    p.updated_at = todayISO();
  }

  function effHtml(p) {
    var eff = effectiveUrl(p);
    if (!eff) return '未填写获取地址';
    return '实际跳转地址：<a class="link-out" href="' + esc(eff) + '" target="_blank" rel="noopener noreferrer">' +
      esc(eff) + '</a>';
  }

  function linkRowHtml(field, label, value, placeholder) {
    var hasVal = !!str(value);
    return '<div class="getlink-row">' +
      '<label class="getlink-label" for="lk-' + esc(field) + '">' + esc(label) + '</label>' +
      '<input id="lk-' + esc(field) + '" class="input getlink-input" type="text" spellcheck="false"' +
      ' data-link="' + esc(field) + '" value="' + esc(value) + '" placeholder="' + esc(placeholder) + '">' +
      '<button type="button" class="btn btn-icon" data-link-open="' + esc(field) + '" title="打开"' +
      (hasVal ? '' : ' disabled') + '>↗</button>' +
      '<button type="button" class="btn btn-icon" data-link-copy="' + esc(field) + '" title="复制"' +
      (hasVal ? '' : ' disabled') + '>⧉</button>' +
      '</div>';
  }

  function linksSectionHtml(p) {
    var any = !!effectiveUrl(p) || !!str(p.pdf);
    return '<section class="drawer-section"><h4>获取地址</h4>' +
      linkRowHtml('doi', 'DOI', p.links.doi, '10.1016/j.artmed.2023.102611') +
      linkRowHtml('arxiv', 'arXiv ID', p.links.arxiv, '2608.17084') +
      linkRowHtml('url', '通用链接', p.links.url, 'https://...') +
      linkRowHtml('pdf', '本地 PDF', p.pdf, '../02_参考文献/xxx.pdf') +
      '<div class="field-note getlink-eff" id="eff-url">' + effHtml(p) + '</div>' +
      '<div class="getlink-empty" id="getlink-empty"' + (any ? ' hidden' : '') + '>' +
      '<div class="field-note">可在 Crossref / Google Scholar 找到 DOI</div>' +
      '<div class="field-note"><a class="link-out" href="https://scholar.google.com/scholar?q=' +
      encodeURIComponent(p.title || p.id) + '" target="_blank" rel="noopener noreferrer">在 Google Scholar 搜索题名</a></div>' +
      '</div>' +
      '</section>';
  }

  /** 编辑中不重绘抽屉（会丢焦点），只刷新派生地址与按钮可用状态。 */
  function refreshLinkDerived(p) {
    var el = $('#eff-url');
    if (el) el.innerHTML = effHtml(p);
    var empty = $('#getlink-empty');
    if (empty) empty.hidden = (!!effectiveUrl(p) || !!str(p.pdf));
    ['doi', 'arxiv', 'url', 'pdf'].forEach(function (f) {
      var ok = !!str(linkValue(p, f));
      $$('[data-link-open="' + f + '"], [data-link-copy="' + f + '"]').forEach(function (b) { b.disabled = !ok; });
    });
  }

  function applyLinkInput(el) {
    var field = el.getAttribute('data-link');
    var p = getPaper(state.openId);
    if (!field || !p) return;
    setLinkValue(p, field, el.value);
    refreshLinkDerived(p);
    afterEdit();
  }

  function blurLinkInput(el) {
    var field = el.getAttribute('data-link');
    var p = getPaper(state.openId);
    if (!field || !p) return;
    var clean = cleanLinkInput(field, el.value);
    if (clean !== el.value) el.value = clean;
    setLinkValue(p, field, clean);
    refreshLinkDerived(p);
    afterEdit();
  }

  function openLinkField(p, field) {
    var v = cleanLinkInput(field, linkValue(p, field));
    if (!v) { toast('尚未填写' + (LINK_LABEL[field] || field)); return; }
    var href = field === 'doi' ? 'https://doi.org/' + v
      : field === 'arxiv' ? 'https://arxiv.org/abs/' + v
        : webSafePath(v);
    window.open(href, '_blank', 'noopener,noreferrer');
  }

  function copyLinkField(p, field) {
    var v = cleanLinkInput(field, linkValue(p, field));
    if (!v) { toast('尚未填写' + (LINK_LABEL[field] || field)); return; }
    copyText(v, '已复制' + (LINK_LABEL[field] || field));
  }

  function chipsEditor(values, vocab, attr) {
    return '<div class="chip-row">' + vocab.map(function (v) {
      var on = values.indexOf(v) >= 0;
      var cls = attr === 'rc' ? ('chip ' + (RC_CLASS[v] || 'bg')) : 'chip chip-cap';
      return '<button type="button" class="' + cls + (on ? ' is-on' : '') + '" data-toggle="' + esc(attr) +
        '" data-value="' + esc(v) + '" aria-pressed="' + (on ? 'true' : 'false') + '">' + esc(v) + '</button>';
    }).join('') + '</div>';
  }

  function selectEditor(field, values, current) {
    return '<select class="select" data-edit="' + esc(field) + '"><option value="">— 未设置 —</option>' +
      values.map(function (v) {
        return '<option value="' + esc(v) + '"' + (v === current ? ' selected' : '') + '>' + esc(v) + '</option>';
      }).join('') + '</select>';
  }

  function textField(label, field, value, rows, note) {
    return '<div class="field">' +
      '<label for="f-' + esc(field) + '">' + esc(label) + (note ? ' <span class="field-note">' + esc(note) + '</span>' : '') + '</label>' +
      '<textarea id="f-' + esc(field) + '" class="textarea' + (rows > 3 ? ' textarea-lg' : '') + '" rows="' + rows +
      '" data-edit="' + esc(field) + '">' + esc(value) + '</textarea>' +
      '</div>';
  }

  function renderDrawer() {
    var drawer = $('#drawer');
    var backdrop = $('#backdrop');
    var p = getPaper(state.openId);

    if (!p) {
      drawer.classList.remove('open');
      drawer.setAttribute('aria-hidden', 'true');
      backdrop.hidden = true;
      return;
    }

    $('#drawer-kicker').textContent = (p.id ? p.id + ' · ' : '') + (p.type || '未分类') +
      (p.tier ? ' · ' + p.tier : '');
    $('#drawer-title').textContent = p.title || '（无标题）';
    $('#drawer-title').title = p.title || '';
    $('#drawer-sub').textContent = p.title_zh || '（无中文译名）';
    var dotEl = $('#drawer-read-dot');
    if (dotEl) {
      dotEl.className = 'read-dot read-' + READ_CLASS[readingState(p)];
      dotEl.title = readTip(p);
    }

    var scoreVal = p.score == null ? '' : String(p.score);
    var body = '';

    // 元信息
    body += '<section class="drawer-section"><h4>元信息</h4><dl class="kv">' +
      '<dt>英文题名</dt><dd>' + dash(p.title) + '</dd>' +
      '<dt>中文译名</dt><dd>' + dash(p.title_zh) + '</dd>' +
      '<dt>作者</dt><dd>' + dash(p.authors || p.first_author) + '</dd>' +
      '<dt>年份</dt><dd>' + (p.year == null ? '—' : esc(p.year)) + '</dd>' +
      '<dt>Venue</dt><dd>' + dash(p.venue) + '</dd>' +
      '<dt>类型</dt><dd>' + dash(p.type) + '</dd>' +
      '<dt>标识</dt><dd>' + dash(p.id) + '</dd>' +
      '<dt>添加 / 更新</dt><dd>' + (dash(p.added_at) + ' / ' + dash(p.updated_at)) + '</dd>' +
      '</dl></section>';

    // 获取地址（可编辑：DOI / arXiv / 通用链接 / 本地 PDF）
    body += linksSectionHtml(p);

    // 映射与状态
    body += '<section class="drawer-section"><h4>映射与状态</h4>' +
      '<div class="field-grid">' +
      '<div class="field"><label for="f-tier">Tier</label>' + selectEditor('tier', TIERS, p.tier) + '</div>' +
      '<div class="field"><label for="f-depth">阅读深度</label>' + selectEditor('depth', DEPTHS, p.depth) + '</div>' +
      '<div class="field"><label for="f-status">状态</label>' + selectEditor('status', STATUSES, p.status) + '</div>' +
      '<div class="field"><label for="f-score">相关度 <span class="field-note" id="score-note">' +
      (scoreVal || '未设置') + '</span></label>' +
      '<input id="f-score" class="input" type="range" min="1" max="5" step="1" value="' + (scoreVal || '3') +
      '" data-edit="score">' +
      '</div></div>' +
      '<div class="field"><label>研究内容 RC <span class="field-note">点击切换</span></label>' +
      chipsEditor(p.rc, RCS, 'rc') + '</div>' +
      '<div class="field"><label>能力标签 caps</label>' + chipsEditor(p.caps, CAPS, 'caps') + '</div>' +
      '</section>';

    // 笔记与摘录
    body += '<section class="drawer-section"><h4>摘录与笔记</h4>' +
      textField('一句话定位', 'one_liner', p.one_liner, 3, '搜索会命中这里') +
      textField('可借鉴', 'borrowable', p.borrowable, 3) +
      textField('未解决 / 缺口', 'gap', p.gap, 3) +
      '<div class="field"><label for="f-keywords">关键词 <span class="field-note">逗号或分号分隔</span></label>' +
      '<input id="f-keywords" class="input" type="text" data-edit="keywords" value="' +
      esc(p.keywords.join('; ')) + '"></div>' +
      '<div class="field"><label for="f-note">Markdown 笔记</label>' +
      '<div class="note-tools"><div class="seg-mini">' +
      '<button type="button" class="' + (state.noteMode === 'write' ? 'is-on' : '') + '" data-note-mode="write">编辑</button>' +
      '<button type="button" class="' + (state.noteMode === 'preview' ? 'is-on' : '') + '" data-note-mode="preview">预览</button>' +
      '</div></div>' +
      '<textarea id="f-note" class="textarea textarea-lg note-editor" rows="10" data-edit="note"' +
      (state.noteMode === 'preview' ? ' hidden' : '') + '>' + esc(p.note) + '</textarea>' +
      '<div class="md-preview" id="note-preview"' + (state.noteMode === 'preview' ? '' : ' hidden') + '>' +
      (state.noteMode === 'preview' ? mdToHtml(p.note) : '') + '</div>' +
      '</div></section>';

    // 操作
    body += '<section class="drawer-section drawer-foot">' +
      '<div class="btn-row">' +
      '<button type="button" class="btn" data-drawer-act="copy-title">复制题名</button>' +
      '<button type="button" class="btn danger" data-drawer-act="revert">还原此篇</button>' +
      '<button type="button" class="btn danger" data-drawer-act="delete">删除此篇</button>' +
      '</div>' +
      '<div class="field-note">所有改动即时写入 localStorage（key: ' + esc(LS_DRAFT) + '）；导出 papers.json 后才算落盘。</div>' +
      '</section>';

    $('#drawer-body').innerHTML = body;
    $('#drawer-body').scrollTop = 0;

    drawer.classList.add('open');
    drawer.setAttribute('aria-hidden', 'false');
    backdrop.hidden = false;
  }

  /* ------------------------------------------------------- Markdown 渲染器 */

  function inlineMd(text) {
    var s2 = esc(text || '');
    var codes = [];
    s2 = s2.replace(/`([^`]+)`/g, function (m, code) {
      codes.push(code);
      return '\u0000C' + (codes.length - 1) + '\u0000';
    });
    s2 = s2.replace(/\*\*([^*]+)\*\*/g, '<strong>$1</strong>');
    s2 = s2.replace(/(^|[\s（(])\*([^*\n]+)\*(?=$|[\s，。；：）)])/g, '$1<em>$2</em>');
    s2 = s2.replace(/\[([^\]]+)\]\((https?:\/\/[^)\s]+)\)/g, function (m, label, href) {
      return '<a href="' + href + '" target="_blank" rel="noopener noreferrer">' + label + '</a>';
    });
    s2 = s2.replace(/\u0000C(\d+)\u0000/g, function (m, i) {
      return '<code>' + codes[Number(i)] + '</code>';
    });
    return s2;
  }

  /** 够用的 Markdown：标题 / 列表 / 引用 / 分隔线 / 粗斜体 / 行内代码 / 链接。 */
  function mdToHtml(src) {
    var lines = String(src == null ? '' : src).replace(/\r\n?/g, '\n').split('\n');
    var html = [];
    var inList = false;
    var inCode = false;
    var codeBuf = [];
    var para = [];

    function flushPara() {
      if (para.length) {
        html.push('<p>' + para.join('<br>') + '</p>');
        para = [];
      }
    }
    function closeList() {
      if (inList) { html.push('</ul>'); inList = false; }
    }

    for (var i = 0; i < lines.length; i++) {
      var line = lines[i];
      var trimmed = line.trim();

      if (/^```/.test(trimmed)) {
        flushPara(); closeList();
        if (inCode) {
          html.push('<pre><code>' + esc(codeBuf.join('\n')) + '</code></pre>');
          codeBuf = []; inCode = false;
        } else {
          inCode = true;
        }
        continue;
      }
      if (inCode) { codeBuf.push(line); continue; }

      if (!trimmed) { flushPara(); closeList(); continue; }

      var h = /^(#{1,6})\s+(.*)$/.exec(trimmed);
      if (h) {
        flushPara(); closeList();
        var level = Math.min(3, h[1].length);
        html.push('<h' + level + ' class="h' + level + '">' + inlineMd(h[2]) + '</h' + level + '>');
        continue;
      }

      if (/^(-{3,}|\*{3,}|_{3,})$/.test(trimmed)) {
        flushPara(); closeList();
        html.push('<hr>');
        continue;
      }

      if (/^>\s?/.test(trimmed)) {
        flushPara(); closeList();
        html.push('<blockquote>' + inlineMd(trimmed.replace(/^>\s?/, '')) + '</blockquote>');
        continue;
      }

      var li = /^[-*+]\s+(.*)$/.exec(trimmed) || /^\d+[.)]\s+(.*)$/.exec(trimmed);
      if (li) {
        flushPara();
        if (!inList) { html.push('<ul>'); inList = true; }
        html.push('<li>' + inlineMd(li[1]) + '</li>');
        continue;
      }

      para.push(inlineMd(trimmed));
    }

    if (inCode) html.push('<pre><code>' + esc(codeBuf.join('\n')) + '</code></pre>');
    flushPara(); closeList();
    return html.join('') || '<p class="dash">还没有笔记。切到「编辑」写 Markdown。</p>';
  }

  /* ----------------------------------------------------------- 导出与下载 */

  function download(filename, text, mime) {
    var blob = new Blob([text], { type: mime || 'text/plain;charset=utf-8' });
    var url = URL.createObjectURL(blob);
    var a = document.createElement('a');
    a.href = url;
    a.download = filename;
    a.rel = 'noopener';
    document.body.appendChild(a);
    a.click();
    setTimeout(function () {
      document.body.removeChild(a);
      URL.revokeObjectURL(url);
    }, 600);
  }

  function exportObject() {
    return {
      version: state.meta.version || 1,
      updated_at: todayISO(),
      exported_at: new Date().toISOString(),
      matrix_overrides: clone(state.overrides),
      papers: clone(state.papers)
    };
  }

  function exportJSON() {
    var obj = exportObject();
    download('papers.json', JSON.stringify(obj, null, 2) + '\n', 'application/json;charset=utf-8');
    markExported('papers.json 已导出（可直接覆盖 data/papers.json）');
  }

  function exportOffline() {
    var obj = exportObject();
    var text = 'window.__PAPERS_OFFLINE__ =\n' + JSON.stringify(obj, null, 2) + ';\n';
    download('papers.offline.js', text, 'text/javascript;charset=utf-8');
    toast('已导出 papers.offline.js（覆盖 data/ 下同名文件后，双击打开即用新数据）');
  }

  /**
   * CSV：列顺序与 06_文献库/papers.csv 前 17 列保持一致，其余字段追加在末尾，
   * 便于和既有 CSV 流程共存；带 UTF-8 BOM，Excel 双击不乱码。
   */
  var CSV_COLUMNS = [
    ['id', function (p) { return p.id; }],
    ['title', function (p) { return p.title; }],
    ['first_author', function (p) { return p.first_author; }],
    ['year', function (p) { return p.year == null ? '' : p.year; }],
    ['venue', function (p) { return p.venue; }],
    ['type', function (p) { return p.type; }],
    ['tier', function (p) { return p.tier; }],
    ['rc', function (p) { return p.rc.join('|'); }],
    ['one_liner', function (p) { return p.one_liner; }],
    ['borrowable', function (p) { return p.borrowable; }],
    ['gap', function (p) { return p.gap; }],
    ['keywords', function (p) { return p.keywords.join(';'); }],
    ['doi_or_arxiv', function (p) { return p.links.doi || p.links.arxiv; }],
    ['url', function (p) { return p.links.url; }],
    ['fulltext', function (p) { return p.pdf ? '本地PDF' : '摘要'; }],
    ['depth', function (p) { return p.depth; }],
    ['note', function (p) { return p.note; }],
    ['title_zh', function (p) { return p.title_zh; }],
    ['caps', function (p) { return p.caps.join('|'); }],
    ['status', function (p) { return p.status; }],
    ['score', function (p) { return p.score == null ? '' : p.score; }],
    ['authors', function (p) { return p.authors; }],
    ['pdf', function (p) { return p.pdf; }],
    ['arxiv', function (p) { return p.links.arxiv; }],
    ['added_at', function (p) { return p.added_at; }],
    ['updated_at', function (p) { return p.updated_at; }],
    ['doi', function (p) { return p.links.doi; }],
    ['effective_url', function (p) { return effectiveUrl(p); }]
  ];

  function csvCell(v) {
    var s2 = String(v == null ? '' : v);
    return '"' + s2.replace(/"/g, '""') + '"';
  }

  function exportCSV() {
    var lines = [CSV_COLUMNS.map(function (c) { return csvCell(c[0]); }).join(',')];
    state.papers.forEach(function (p) {
      lines.push(CSV_COLUMNS.map(function (c) { return csvCell(c[1](p)); }).join(','));
    });
    var text = '\ufeff' + lines.join('\r\n') + '\r\n';
    download('papers.csv', text, 'text/csv;charset=utf-8');
    markExported('papers.csv 已导出（UTF-8 BOM，Excel 可直接打开）');
  }

  function mdCiteLine(p) {
    var who = p.first_author || p.authors || '—';
    var year = p.year == null ? '—' : p.year;
    var venue = p.venue ? ', ' + p.venue : '';
    return '- **' + who + ' et al. (' + year + ')' + venue + '** — ' + (p.one_liner || '（无一句话定位）') + '\n' +
      '  - 可借鉴：' + (p.borrowable || '—') + '\n' +
      '  - 未解决：' + (p.gap || '—') + '\n' +
      '  - 获取地址：' + (effectiveUrl(p) || '未填写');
  }

  function exportMD() {
    var out = [];
    out.push('# 文献映射（按研究内容分组）');
    out.push('');
    out.push('> 由「研究文献映射库」导出于 ' + todayISO() + '；共 ' + state.papers.length + ' 篇。');
    out.push('');

    var sections = RCS.map(function (rc) {
      return { key: rc, title: '## ' + rc + ' ' + (RC_FULL[rc] || '').replace(/^背景.*$/, '') };
    });
    sections.push({ key: '__none', title: '## 未映射 RC' });

    sections.forEach(function (sec) {
      var items = state.papers.filter(function (p) {
        return sec.key === '__none' ? p.rc.length === 0 : p.rc.indexOf(sec.key) >= 0;
      });
      if (!items.length) return;
      items = sortPapers(items);
      out.push(sec.title.trim());
      out.push('');
      items.forEach(function (p) { out.push(mdCiteLine(p)); });
      out.push('');
    });

    download('文献映射-' + todayISO() + '.md', out.join('\n'), 'text/markdown;charset=utf-8');
    toast('已导出 Markdown（按 RC 分组）');
  }

  /** 导出后：把当前状态视为新的基线，清掉“未导出”计数，但保留 localStorage 草稿以防误覆盖。 */
  function markExported(msg) {
    state.baseline = clone(state.papers);
    state.baseOverrides = clone(state.overrides);
    state.dirtyCount = 0;
    renderDirty();
    saveDraftNow();
    toast(msg);
  }

  /* ------------------------------------------------------------- 提示浮层 */

  var toastTimer = null;
  function toast(msg, opts) {
    var el = $('#toast');
    var action = opts && opts.action;
    el.innerHTML = '<span class="toast-msg">' + esc(msg) + '</span>' +
      (action ? '<button type="button" class="toast-act">' + esc(action) + '</button>' : '');
    el.classList.toggle('has-action', !!action);
    el.hidden = false;
    el.classList.add('is-on');
    if (toastTimer) clearTimeout(toastTimer);
    var dur = (opts && opts.duration) || 2600;
    function hide() { el.classList.remove('is-on'); el.hidden = true; }
    if (action) {
      var btn = el.querySelector('.toast-act');
      if (btn) {
        btn.addEventListener('click', function () {
          hide();
          if (toastTimer) clearTimeout(toastTimer);
          if (typeof opts.onAction === 'function') opts.onAction();
        });
      }
    }
    toastTimer = setTimeout(hide, dur);
  }

  function tooltipShow(title, sub, x, y) {
    var el = $('#tooltip');
    el.innerHTML = '<div class="tooltip-title">' + esc(title) + '</div>' +
      (sub ? '<div class="tooltip-sub">' + esc(sub) + '</div>' : '');
    el.hidden = false;
    el.classList.add('is-on');
    moveTooltip(x, y);
  }

  function moveTooltip(x, y) {
    var el = $('#tooltip');
    var w = el.offsetWidth || 240, h = el.offsetHeight || 60;
    var left = Math.min(window.innerWidth - w - 12, x + 14);
    var top = y + 16;
    if (top + h > window.innerHeight - 8) top = y - h - 12;
    el.style.left = Math.max(8, left) + 'px';
    el.style.top = Math.max(8, top) + 'px';
  }

  function tooltipHide() {
    var el = $('#tooltip');
    el.hidden = true;
    el.classList.remove('is-on');
  }

  /* --------------------------------------------------------------- 模态框 */

  function openModal(opts) {
    var card = $('#modal-card');
    card.classList.remove('is-wide');
    var actions = (opts.actions || []).map(function (a, i) {
      return '<button type="button" class="btn ' + (a.cls || '') + '" data-modal-idx="' + i + '">' +
        esc(a.label) + '</button>';
    }).join('');
    card.innerHTML = '<div class="modal-title">' + esc(opts.title) + '</div>' +
      '<div class="modal-text">' + (opts.html || '') + '</div>' +
      '<div class="modal-actions">' + actions + '</div>';
    $('#modal').hidden = false;

    card.querySelectorAll('[data-modal-idx]').forEach(function (btn) {
      btn.addEventListener('click', function () {
        var idx = Number(btn.getAttribute('data-modal-idx'));
        var act = (opts.actions || [])[idx];
        closeModal();
        if (act && typeof act.onClick === 'function') act.onClick();
      });
    });
    var first = card.querySelector('.modal-actions .btn');
    if (first) first.focus();
  }

  function closeModal() {
    $('#modal').hidden = true;
    var card = $('#modal-card');
    if (card) card.classList.remove('is-wide');
  }

  /* ------------------------------------------------------------- 交互动作 */

  var dragId = null;

  function syncSearchInput() {
    var el = $('#search-input');
    if (el) el.value = state.q;
  }

  function clearFilters() {
    state.filters = { tier: [], rc: [], depth: [], status: [], read: [], yearFrom: null, yearTo: null, venue: '' };
    state.q = '';
    syncSearchInput();
    render();
  }

  function toggleSort(key) {
    if (state.sort.key === key) {
      state.sort.dir = state.sort.dir === 'desc' ? 'asc' : 'desc';
    } else {
      state.sort = { key: key, dir: key === 'venue' || key === 'tier' ? 'asc' : 'desc' };
    }
    render();
  }

  function applyYearInputs() {
    var a = parseInt($('#year-from').value, 10);
    var b = parseInt($('#year-to').value, 10);
    var from = isFinite(a) ? a : null;
    var to = isFinite(b) ? b : null;
    if (from != null && to != null && from > to) { var t = from; from = to; to = t; }
    state.filters.yearFrom = from;
    state.filters.yearTo = to;
    render();
  }

  function afterEdit() {
    state.dirtyCount = computeDirtyCount();
    saveDraftSoon();
    renderDirty();
    renderView();
  }

  function openDrawer(id) {
    if (!getPaper(id)) return;
    state.openId = id;
    state.selectedId = id;
    state.noteMode = 'write';
    renderDrawer();
    var btn = $('#drawer-close');
    if (btn) { try { btn.focus({ preventScroll: true }); } catch (e) { /* 忽略 */ } }
  }

  function closeDrawer() {
    state.openId = null;
    renderDrawer();
    tooltipHide();
  }

  /** 抽屉里的字段编辑：写 state → 计入未导出修改 → 落 localStorage → 刷新主区。 */
  function applyEdit(el) {
    var field = el.getAttribute('data-edit');
    if (!field) return;
    var p = getPaper(state.openId);
    if (!p) return;

    if (field === 'keywords') {
      p.keywords = el.value.split(/[;；,，]/).map(function (t) { return t.trim(); }).filter(Boolean);
    } else if (field === 'score') {
      var n = Number(el.value);
      p.score = isFinite(n) ? Math.min(5, Math.max(1, Math.round(n))) : null;
      var sn = $('#score-note');
      if (sn) sn.textContent = p.score == null ? '未设置' : String(p.score);
    } else if (field === 'note') {
      p.note = el.value;
      if (state.noteMode === 'preview') {
        var pv = $('#note-preview');
        if (pv) pv.innerHTML = mdToHtml(p.note);
      }
    } else {
      p[field] = el.value;
    }

    p.updated_at = todayISO();
    afterEdit();
  }

  function togglePaperChip(chip) {
    var p = getPaper(state.openId);
    if (!p) return;
    var field = chip.getAttribute('data-toggle');
    var val = chip.getAttribute('data-value');
    var arr = field === 'rc' ? p.rc : p.caps;
    var i = arr.indexOf(val);
    if (i >= 0) arr.splice(i, 1); else arr.push(val);
    var on = i < 0;
    chip.classList.toggle('is-on', on);
    chip.setAttribute('aria-pressed', on ? 'true' : 'false');
    p.updated_at = todayISO();
    afterEdit();
  }

  function revertPaper(id) {
    var b = null;
    for (var i = 0; i < state.baseline.length; i++) {
      if (state.baseline[i].id === id) { b = state.baseline[i]; break; }
    }
    var p = getPaper(id);
    if (!b || !p) return;
    EDIT_FIELDS.forEach(function (k) {
      if (Array.isArray(b[k])) p[k] = b[k].slice();
      else if (b[k] && typeof b[k] === 'object') p[k] = clone(b[k]);  // links 等对象必须深拷贝，避免污染 baseline
      else p[k] = b[k];
    });
    Object.keys(state.overrides).forEach(function (k) {
      if (k.indexOf(id + '|') === 0) delete state.overrides[k];
    });
    state.dirtyCount = computeDirtyCount();
    saveDraftSoon();
    renderDirty();
    renderView();
    renderDrawer();
    toast('已还原此篇到 papers.json 的状态');
  }

  /* --------------------------------------------------------- 添加 / 删除文献 */

  function padNum(n, width) {
    var s = String(n);
    while (s.length < width) s = '0' + s;
    return s;
  }

  /** id 规则：扫描全部 P<数字> 取最大值 +1，至少 3 位补零，冲突继续递增。 */
  function nextPaperId() {
    var max = 0;
    state.papers.forEach(function (p) {
      var m = /^P(\d+)$/.exec(p.id);
      if (m) {
        var n = parseInt(m[1], 10);
        if (n > max) max = n;
      }
    });
    var n = max + 1;
    var width = Math.max(3, String(n).length);
    var taken = {};
    state.papers.forEach(function (p) { taken[p.id] = true; });
    var id = 'P' + padNum(n, width);
    while (taken[id]) { n += 1; id = 'P' + padNum(n, width); }
    return id;
  }

  function emptyAddValues() {
    return {
      title: '', title_zh: '', first_author: '', year: '', venue: '', type: '方法',
      tier: 'T2', score: '3', depth: '题名', status: '待读', rc: [],
      doi: '', arxiv: '', url: '', pdf: '', one_liner: ''
    };
  }

  function addEl(key) { return $('#add-form [data-add="' + key + '"]'); }

  function addFormHtml(v) {
    var scoreNote = esc(v.score || '3');
    return '<form id="add-form" class="add-form" novalidate>' +
      '<div class="field add-full">' +
      '<label for="add-title">英文题名 <span class="field-note">必填</span></label>' +
      '<input id="add-title" class="input" type="text" data-add="title" value="' + esc(v.title) +
      '" placeholder="Paper title in English" autocomplete="off">' +
      '<div class="field-error" id="err-title" hidden></div></div>' +

      '<div class="field add-full"><label for="add-title-zh">中文译名</label>' +
      '<input id="add-title-zh" class="input" type="text" data-add="title_zh" value="' + esc(v.title_zh) + '"></div>' +

      '<div class="add-row">' +
      '<div class="field"><label for="add-author">第一作者</label>' +
      '<input id="add-author" class="input" type="text" data-add="first_author" value="' + esc(v.first_author) + '"></div>' +
      '<div class="field"><label for="add-year">年份</label>' +
      '<input id="add-year" class="input" type="number" inputmode="numeric" min="1900" max="2100" data-add="year" value="' +
      esc(v.year) + '" placeholder="2023">' +
      '<div class="field-error" id="err-year" hidden></div></div>' +
      '</div>' +

      '<div class="add-row">' +
      '<div class="field"><label for="add-venue">Venue</label>' +
      '<input id="add-venue" class="input" type="text" data-add="venue" value="' + esc(v.venue) + '"></div>' +
      '<div class="field"><label for="add-type">类型</label>' +
      '<select id="add-type" class="select" data-add="type">' +
      TYPES.map(function (t) {
        return '<option value="' + esc(t) + '"' + (t === v.type ? ' selected' : '') + '>' + esc(t) + '</option>';
      }).join('') + '</select></div></div>' +

      '<div class="add-row">' +
      '<div class="field"><label for="add-tier">Tier</label>' +
      '<select id="add-tier" class="select" data-add="tier">' +
      TIERS.map(function (t) {
        return '<option value="' + esc(t) + '"' + (t === v.tier ? ' selected' : '') + '>' + esc(t) + ' ' + esc(TIER_NOTE[t]) + '</option>';
      }).join('') + '</select></div>' +
      '<div class="field"><label for="add-score">相关度 <span class="field-note" id="add-score-note">' + scoreNote + '</span></label>' +
      '<input id="add-score" class="input" type="range" min="1" max="5" step="1" data-add="score" value="' + esc(v.score || '3') + '"></div></div>' +

      '<div class="add-row">' +
      '<div class="field"><label for="add-depth">阅读深度</label>' +
      '<select id="add-depth" class="select" data-add="depth">' +
      DEPTHS.map(function (d) {
        return '<option value="' + esc(d) + '"' + (d === v.depth ? ' selected' : '') + '>' + esc(d) + '</option>';
      }).join('') + '</select></div>' +
      '<div class="field"><label for="add-status">状态</label>' +
      '<select id="add-status" class="select" data-add="status">' +
      STATUSES.map(function (s) {
        return '<option value="' + esc(s) + '"' + (s === v.status ? ' selected' : '') + '>' + esc(s) + '</option>';
      }).join('') + '</select></div></div>' +

      '<div class="field add-full"><label>研究内容 RC <span class="field-note">可多选，可留空</span></label>' +
      '<div class="chip-row">' + RCS.map(function (r) {
        var on = v.rc.indexOf(r) >= 0;
        return '<button type="button" class="chip chip-' + (RC_CLASS[r] || 'bg') + (on ? ' is-on' : '') +
          '" data-pick="rc" data-value="' + esc(r) + '" aria-pressed="' + (on ? 'true' : 'false') + '">' + esc(r) + '</button>';
      }).join('') + '</div></div>' +

      '<div class="add-row">' +
      '<div class="field"><label for="add-doi">DOI</label>' +
      '<input id="add-doi" class="input" type="text" data-add="doi" value="' + esc(v.doi) + '" placeholder="10.1016/..."></div>' +
      '<div class="field"><label for="add-arxiv">arXiv ID</label>' +
      '<input id="add-arxiv" class="input" type="text" data-add="arxiv" value="' + esc(v.arxiv) + '" placeholder="2608.17084"></div>' +
      '</div>' +

      '<div class="field add-full"><label for="add-url">通用链接</label>' +
      '<input id="add-url" class="input" type="text" data-add="url" value="' + esc(v.url) + '" placeholder="https://..."></div>' +

      '<div class="field add-full"><label for="add-pdf">本地 PDF 相对路径 <span class="field-note">可选</span></label>' +
      '<input id="add-pdf" class="input" type="text" data-add="pdf" value="' + esc(v.pdf) + '" placeholder="../02_参考文献/xxx.pdf"></div>' +

      '<div class="field add-full"><label for="add-one">一句话定位 <span class="field-note">可选</span></label>' +
      '<textarea id="add-one" class="textarea" rows="2" data-add="one_liner">' + esc(v.one_liner) + '</textarea></div>' +
      '</form>';
  }

  function readAddValues() {
    var keys = ['title', 'title_zh', 'first_author', 'year', 'venue', 'type', 'tier', 'score',
      'depth', 'status', 'doi', 'arxiv', 'url', 'pdf', 'one_liner'];
    var v = {};
    keys.forEach(function (k) {
      var el = addEl(k);
      v[k] = el ? String(el.value) : '';
    });
    v.rc = $$('#add-form .chip[data-pick="rc"].is-on').map(function (b) {
      return b.getAttribute('data-value');
    });
    return v;
  }

  function showAddErrors(errs) {
    var map = { title: 'err-title', year: 'err-year' };
    Object.keys(map).forEach(function (k) {
      var el = $('#' + map[k]);
      if (!el) return;
      var msg = errs[k] || '';
      el.textContent = msg;
      el.hidden = !msg;
      var input = addEl(k);
      if (input) input.classList.toggle('is-invalid', !!msg);
    });
    if (errs.title) { var t = $('#add-title'); if (t) t.focus(); }
    else if (errs.year) { var y = $('#add-year'); if (y) y.focus(); }
  }

  function validateAddValues(v) {
    var errs = {};
    if (!str(v.title)) errs.title = '英文题名不能为空';
    var y = str(v.year);
    if (y) {
      var n = Number(y);
      if (!/^\d{4}$/.test(y) || n < 1900 || n > 2100) errs.year = '年份需为 1900–2100 的四位数字，或留空';
    }
    return errs;
  }

  function newPaperFromValues(v) {
    var today = todayISO();
    var year = str(v.year) ? Number(v.year) : null;
    var score = Number(v.score);
    if (!isFinite(score)) score = 3;
    score = Math.min(5, Math.max(1, Math.round(score)));
    var rc = v.rc.filter(function (x) { return RCS.indexOf(x) >= 0; });
    return {
      id: nextPaperId(),
      title: str(v.title),
      title_zh: str(v.title_zh),
      authors: '',
      first_author: str(v.first_author),
      year: year,
      venue: str(v.venue),
      type: TYPES.indexOf(v.type) >= 0 ? v.type : '方法',
      tier: TIERS.indexOf(v.tier) >= 0 ? v.tier : 'T2',
      rc: rc,
      caps: [],
      depth: DEPTHS.indexOf(v.depth) >= 0 ? v.depth : '题名',
      status: STATUSES.indexOf(v.status) >= 0 ? v.status : '待读',
      score: score,
      one_liner: str(v.one_liner),
      borrowable: '',
      gap: '',
      keywords: [],
      links: {
        doi: cleanLinkInput('doi', v.doi),
        arxiv: cleanLinkInput('arxiv', v.arxiv),
        url: cleanLinkInput('url', v.url)
      },
      pdf: str(v.pdf),
      note: '',
      added_at: today,
      updated_at: today
    };
  }

  function submitAddForm() {
    var v = readAddValues();
    var errs = validateAddValues(v);
    showAddErrors(errs);
    if (Object.keys(errs).length) return;
    var p = newPaperFromValues(v);
    closeModal();
    state.papers.unshift(p);
    state.selectedId = p.id;
    afterEdit();
    openDrawer(p.id);
    var visible = filtered().some(function (x) { return x.id === p.id; });
    if (visible) {
      toast('已添加 ' + p.id + '，接着补笔记吧');
    } else {
      toast('已添加 ' + p.id + '，但当前筛选条件下不可见', {
        action: '清除筛选', duration: 6000, onAction: clearFilters
      });
    }
  }

  function requestAddCancel() {
    var v = readAddValues();
    var dirty = ['title', 'title_zh', 'first_author', 'year', 'venue', 'doi', 'arxiv', 'url', 'pdf', 'one_liner']
      .some(function (k) { return !!str(v[k]); }) || v.rc.length > 0 || v.type !== '方法' ||
      v.tier !== 'T2' || v.score !== '3' || v.depth !== '题名' || v.status !== '待读';
    if (!dirty) { closeModal(); return; }
    openModal({
      title: '放弃这篇文献？',
      html: '<p>表单里已经填了内容，取消后不会保存。确定放弃？</p>',
      actions: [
        { label: '继续填写', cls: 'btn-strong', onClick: function () { openAddPaperModal(v); } },
        { label: '放弃', cls: 'danger', onClick: function () { closeModal(); } }
      ]
    });
  }

  function openAddPaperModal(values) {
    var v = values || emptyAddValues();
    var card = $('#modal-card');
    card.classList.add('is-wide');
    card.innerHTML = '<div class="modal-title">添加文献</div>' +
      '<div class="modal-text add-modal-text">' + addFormHtml(v) + '</div>' +
      '<div class="modal-actions">' +
      '<span class="field-note add-shortcut">Ctrl+Enter 确定 · Esc 取消</span>' +
      '<button type="button" class="btn" data-add-cancel>取消</button>' +
      '<button type="button" class="btn btn-strong" data-add-submit>确定</button>' +
      '</div>';
    $('#modal').hidden = false;
    bindAddForm();
    var cb = card.querySelector('[data-add-cancel]');
    if (cb) cb.addEventListener('click', requestAddCancel);
    var sb = card.querySelector('[data-add-submit]');
    if (sb) sb.addEventListener('click', submitAddForm);
    var t = $('#add-title');
    if (t) { try { t.focus({ preventScroll: true }); } catch (e) { t.focus(); } }
  }

  function bindAddForm() {
    var form = $('#add-form');
    if (!form) return;
    form.addEventListener('submit', function (e) { e.preventDefault(); submitAddForm(); });
    form.addEventListener('keydown', function (e) {
      if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') { e.preventDefault(); submitAddForm(); }
    });
    form.addEventListener('click', function (e) {
      var chip = e.target.closest('.chip[data-pick="rc"]');
      if (!chip) return;
      var on = chip.classList.toggle('is-on');
      chip.setAttribute('aria-pressed', on ? 'true' : 'false');
    });
    var sc = $('#add-score');
    if (sc) {
      sc.addEventListener('input', function () {
        var note = $('#add-score-note');
        if (note) note.textContent = sc.value;
      });
    }
  }

  function requestModalEscape() {
    if ($('#add-form')) { requestAddCancel(); return; }
    closeModal();
  }

  /* --------------------------------------------------------------- 删除 */

  function confirmDelete(id) {
    var p = getPaper(id);
    if (!p) return;
    openModal({
      title: '删除文献',
      html: '<p>确认删除下面这篇？</p>' +
        '<p class="confirm-title">' + esc(p.title || p.id) + '</p>' +
        '<p class="field-note">删除会同时清掉它在矩阵里的三态覆盖；8 秒内可撤销（恢复原位置与覆盖）。</p>',
      actions: [
        { label: '取消' },
        { label: '删除', cls: 'danger', onClick: function () { deletePaper(id); } }
      ]
    });
  }

  function deletePaper(id) {
    var idx = -1;
    for (var i = 0; i < state.papers.length; i++) {
      if (state.papers[i].id === id) { idx = i; break; }
    }
    if (idx < 0) return;
    var paper = state.papers[idx];
    var ov = {};
    Object.keys(state.overrides).forEach(function (k) {
      if (k.indexOf(id + '|') === 0) { ov[k] = state.overrides[k]; delete state.overrides[k]; }
    });
    state.papers.splice(idx, 1);
    if (state.selectedId === id) state.selectedId = null;
    if (state.openId === id) { state.openId = null; renderDrawer(); }
    afterEdit();
    toast('已删除《' + (paper.title || paper.id) + '》', {
      action: '撤销',
      duration: 8000,
      onAction: function () { undoDelete(paper, idx, ov); }
    });
  }

  function undoDelete(paper, idx, ov) {
    if (getPaper(paper.id)) { toast('撤销失败：该 id 已存在'); return; }
    var at = Math.max(0, Math.min(idx, state.papers.length));
    state.papers.splice(at, 0, paper);
    Object.keys(ov).forEach(function (k) { state.overrides[k] = ov[k]; });
    state.selectedId = paper.id;
    afterEdit();
    toast('已撤销删除《' + (paper.title || paper.id) + '》');
  }

  function copyText(text, okMsg) {
    var msg = okMsg || '已复制';
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).then(function () {
        toast(msg);
      }, function () {
        legacyCopy(text, msg);
      });
    } else {
      legacyCopy(text, msg);
    }
  }

  function legacyCopy(text, msg) {
    var ta = document.createElement('textarea');
    ta.value = text;
    ta.setAttribute('readonly', '');
    ta.style.position = 'fixed';
    ta.style.top = '-1000px';
    ta.style.opacity = '0';
    document.body.appendChild(ta);
    ta.select();
    var ok = false;
    try { ok = document.execCommand('copy'); } catch (e) { ok = false; }
    document.body.removeChild(ta);
    toast(ok ? msg : '复制失败，请手动从地址栏复制');
  }

  function openMenu(show) {
    var menu = $('#export-menu');
    var btn = $('#export-btn');
    if (!menu || !btn) return;
    menu.hidden = !show;
    btn.setAttribute('aria-expanded', show ? 'true' : 'false');
  }

  /* ------------------------------------------------------------ 草稿与重载 */

  /**
   * 以草稿为准：草稿是保存当时的完整快照。
   * - baseline 里有、草稿里没有 → 用户删除了，不能补回（否则删除刷新即复活）；
   * - 草稿里有、baseline 里没有 → 用户新增的，保留；
   * - 数据文件在草稿保存后更新过 → 把文件里新增的条目补进来，避免丢外部更新。
   */
  function mergeDraft(draft) {
    var list = (draft.papers || []).map(function (raw, i) { return normalizePaper(raw, i); });
    var seen = {};
    list.forEach(function (p) { seen[p.id] = true; });
    var verChanged = (String(draft.baseUpdatedAt || '') !== String(state.meta.updatedAt || '')) ||
      (String(draft.baseVersion || '') !== String(state.meta.version || ''));
    if (verChanged) {
      state.baseline.forEach(function (b) {
        if (!seen[b.id]) { list.push(clone(b)); seen[b.id] = true; }
      });
    }
    state.papers = list;
    state.overrides = normalizeOverrides(draft.matrix_overrides);
  }

  function discardDraft() {
    clearDraft();
    state.papers = clone(state.baseline);
    state.overrides = clone(state.baseOverrides);
    state.dirtyCount = 0;
    if (state.openId) renderDrawer();
    render();
    toast('已丢弃本地草稿，以 papers.json 为准');
  }

  function promptDraft(dra, n) {
    var when = '未知时间';
    try {
      if (dra.savedAt) when = new Date(dra.savedAt).toLocaleString('zh-CN', { hour12: false });
    } catch (e) { /* 忽略 */ }

    var verChanged = (String(dra.baseUpdatedAt || '') !== String(state.meta.updatedAt || '')) ||
      (String(dra.baseVersion || '') !== String(state.meta.version || ''));

    var html = '<p>浏览器 localStorage 里存有一份草稿，与当前数据相差 <b>' + n + '</b> 处，保存于 ' + esc(when) + '。</p>' +
      (verChanged
        ? '<p>注意：数据文件版本与草稿基线不同（草稿基于 ' + esc(dra.baseUpdatedAt || '未知') +
        '，当前为 ' + esc(state.meta.updatedAt || '未知') + '）。继续使用草稿时，新条目会以 papers.json 为准保留。</p>'
        : '') +
      '<p>继续使用草稿，还是丢弃草稿（以 papers.json 为准）？</p>';

    openModal({
      title: '检测到未导出的修改',
      html: html,
      actions: [
        {
          label: '继续使用草稿', cls: 'btn-strong', onClick: function () {
            state.dirtyCount = computeDirtyCount();
            render();
            toast('已继续使用本地草稿（' + state.dirtyCount + ' 处修改）');
          }
        },
        { label: '丢弃草稿', cls: 'danger', onClick: discardDraft }
      ]
    });
  }

  async function reloadFromDisk() {
    clearDraft();
    try {
      var loaded = await loadData();
      state.dataSource = loaded.source;
      applyData(loaded.json);
      buildVenueOptions();
      state.openId = null;
      state.dirtyCount = 0;
      renderDrawer();
      render();
      toast('已重新加载数据，本地草稿已清空');
    } catch (err) {
      toast('重新加载失败：' + (err && err.message ? err.message : err));
    }
  }

  function confirmReload() {
    openModal({
      title: '放弃本地修改，重新加载',
      html: '<p>将清空 localStorage 草稿（当前 <b>' + state.dirtyCount + '</b> 处未导出修改），' +
        '并从 papers.json（或离线副本）重新读取。此操作不可撤销。</p>',
      actions: [
        { label: '取消', cls: '' },
        { label: '确认丢弃并重载', cls: 'danger', onClick: reloadFromDisk }
      ]
    });
  }

  /* --------------------------------------------------------------- 主题 */

  function initTheme() {
    var t = 'auto';
    try { t = localStorage.getItem(LS_THEME) || 'auto'; } catch (e) { t = 'auto'; }
    if (['auto', 'light', 'dark'].indexOf(t) < 0) t = 'auto';
    setTheme(t);
  }

  function setTheme(t) {
    state.theme = t;
    document.documentElement.setAttribute('data-theme', t);
    try { localStorage.setItem(LS_THEME, t); } catch (e) { /* 忽略 */ }
    var b = $('#theme-btn');
    if (b) {
      b.textContent = t === 'dark' ? '●' : (t === 'light' ? '○' : '◐');
      b.title = '主题：' + ({ auto: '跟随系统', light: '浅色', dark: '深色' }[t] || '跟随系统') + '（点击切换）';
    }
  }

  /* --------------------------------------------------------------- 事件 */

  function buildVenueOptions() {
    var sel = $('#venue-select');
    if (!sel) return;
    var counts = {};
    state.papers.forEach(function (p) {
      var v = str(p.venue);
      if (!v) return;
      counts[v] = (counts[v] || 0) + 1;
    });
    var names = Object.keys(counts).sort(function (a, b) {
      if (counts[b] !== counts[a]) return counts[b] - counts[a];
      return a.localeCompare(b);
    });
    sel.innerHTML = '<option value="">全部 venue（' + names.length + '）</option>' +
      names.map(function (n) {
        return '<option value="' + esc(n) + '">' + esc(n) + ' · ' + counts[n] + '</option>';
      }).join('');
    if (state.filters.venue && !counts[state.filters.venue]) state.filters.venue = '';
    sel.value = state.filters.venue;
  }

  function bindEvents() {
    /* 搜索 */
    var search = $('#search-input');
    var searchSoon = debounce(function () { state.q = search.value; render(); }, 120);
    search.addEventListener('input', searchSoon);
    search.addEventListener('keydown', function (e) {
      if (e.key === 'Escape') {
        e.stopPropagation();
        state.q = '';
        search.value = '';
        render();
      }
    });
    $('#search-clear').addEventListener('click', function () {
      state.q = '';
      search.value = '';
      render();
      search.focus();
    });

    /* 视图切换 */
    $('#viewtabs').addEventListener('click', function (e) {
      var b = e.target.closest('.viewtab');
      if (!b) return;
      var v = b.getAttribute('data-view');
      if (v === state.view) return;
      state.view = v;
      render();
    });

    /* 左侧筛选 */
    $('#filters').addEventListener('click', function (e) {
      var chip = e.target.closest('.chip-row[data-filter] .chip');
      if (chip) {
        var row = chip.closest('.chip-row[data-filter]');
        var name = row.getAttribute('data-filter');
        var val = chip.getAttribute('data-value');
        var arr = state.filters[name];
        var i = arr.indexOf(val);
        if (i >= 0) arr.splice(i, 1); else arr.push(val);
        render();
        return;
      }
      if (e.target.closest('#clear-filters')) clearFilters();
    });

    $('#year-from').addEventListener('change', applyYearInputs);
    $('#year-to').addEventListener('change', applyYearInputs);
    $('#venue-select').addEventListener('change', function (e) {
      state.filters.venue = e.target.value;
      render();
    });
    $('#group-toggle').addEventListener('change', function (e) {
      state.groupTier = e.target.checked;
      render();
    });

    /* 添加文献：顶部 + 列表工具栏双入口 */
    var addBtn = $('#add-paper-btn');
    if (addBtn) addBtn.addEventListener('click', function () { openAddPaperModal(); });
    var listAdd = $('#list-add-btn');
    if (listAdd) listAdd.addEventListener('click', function () { openAddPaperModal(); });

    /* 阅读状态文字标签（存 localStorage） */
    var rlt = $('#read-label-toggle');
    if (rlt) {
      rlt.addEventListener('change', function () {
        state.readLabel = rlt.checked;
        saveReadLabelPref(state.readLabel);
        document.body.classList.toggle('show-read-labels', state.readLabel);
        render();
      });
    }
    $('#matrix-t1').addEventListener('change', function (e) {
      state.matrixT1 = e.target.checked;
      render();
    });

    /* 分段按钮 */
    $('#matrix-dim').addEventListener('click', function (e) {
      var b = e.target.closest('[data-dim]');
      if (!b) return;
      state.matrixDim = b.getAttribute('data-dim');
      render();
    });
    $('#timeline-group').addEventListener('click', function (e) {
      var b = e.target.closest('[data-group]');
      if (!b) return;
      state.timelineGroup = b.getAttribute('data-group');
      render();
    });

    /* 列表：排序 / 分组折叠 / 打开抽屉 */
    $('#list-host').addEventListener('click', function (e) {
      var th = e.target.closest('th[data-sort]');
      if (th) { toggleSort(th.getAttribute('data-sort')); return; }
      var head = e.target.closest('.tier-group-head');
      if (head) {
        var k = head.getAttribute('data-group');
        state.collapsed[k] = !state.collapsed[k];
        render();
        return;
      }
      var del = e.target.closest('.row-del');
      if (del) {
        e.stopPropagation();
        confirmDelete(del.getAttribute('data-del'));
        return;
      }
      // 圆点与 ↗ 不打开抽屉（圆点完全无动作；↗ 走浏览器默认新标签）
      if (e.target.closest('.cell-read') || e.target.closest('.title-link')) return;
      var tr = e.target.closest('tr.row');
      if (tr) {
        $$('#list-host tr.row.is-active').forEach(function (r) { r.classList.remove('is-active'); });
        tr.classList.add('is-active');
        openDrawer(tr.getAttribute('data-id'));
      }
    });
    $('#list-host').addEventListener('keydown', function (e) {
      if (e.key !== 'Enter' && e.key !== ' ') return;
      var head = e.target.closest('.tier-group-head');
      if (!head) return;
      e.preventDefault();
      var k = head.getAttribute('data-group');
      state.collapsed[k] = !state.collapsed[k];
      render();
    });

    /* 看板拖拽 */
    var board = $('#board-host');
    board.addEventListener('dragstart', function (e) {
      var card = e.target.closest('.card');
      if (!card) return;
      dragId = card.getAttribute('data-id');
      card.classList.add('is-dragging');
      try {
        e.dataTransfer.setData('text/plain', dragId);
        e.dataTransfer.effectAllowed = 'move';
      } catch (err) { /* 忽略 */ }
    });
    board.addEventListener('dragend', function (e) {
      var card = e.target.closest('.card');
      if (card) card.classList.remove('is-dragging');
      $$('.board-col.is-over', board).forEach(function (c) { c.classList.remove('is-over'); });
    });
    board.addEventListener('dragover', function (e) {
      var col = e.target.closest('.board-col');
      if (!col) return;
      e.preventDefault();
      try { e.dataTransfer.dropEffect = 'move'; } catch (err) { /* 忽略 */ }
      $$('.board-col.is-over', board).forEach(function (c) {
        if (c !== col) c.classList.remove('is-over');
      });
      col.classList.add('is-over');
    });
    board.addEventListener('dragleave', function (e) {
      var col = e.target.closest('.board-col');
      if (col && !col.contains(e.relatedTarget)) col.classList.remove('is-over');
    });
    board.addEventListener('drop', function (e) {
      var col = e.target.closest('.board-col');
      if (!col) return;
      e.preventDefault();
      var depth = col.getAttribute('data-depth');
      var id = dragId;
      try { id = e.dataTransfer.getData('text/plain') || dragId; } catch (err) { id = dragId; }
      var p = getPaper(id);
      col.classList.remove('is-over');
      if (!p) return;
      if (depth === '未标注') depth = '';
      if (p.depth === depth) return;
      p.depth = depth;
      p.updated_at = todayISO();
      afterEdit();
      toast('已移到「' + (depth || '未标注') + '」，depth 已更新并计入未导出修改');
    });
    board.addEventListener('click', function (e) {
      if (e.target.closest('.card-link')) return;
      var card = e.target.closest('.card');
      if (card) openDrawer(card.getAttribute('data-id'));
    });
    board.addEventListener('keydown', function (e) {
      if (e.key !== 'Enter' || !e.target.closest('.card')) return;
      openDrawer(e.target.closest('.card').getAttribute('data-id'));
    });

    /* 矩阵：单元格三态循环 */
    $('#matrix-host').addEventListener('click', function (e) {
      var td = e.target.closest('td.cell');
      if (!td) return;
      var id = td.getAttribute('data-id');
      var col = td.getAttribute('data-col');
      var dim = td.getAttribute('data-dim');
      var p = getPaper(id);
      if (!p) return;
      var cur = cellState(p, dim, col);
      var next = (cur + 1) % 3;
      var key = cellKey(id, dim, col);
      if (next === derivedState(p, dim, col)) delete state.overrides[key];
      else state.overrides[key] = next;
      afterEdit();
    });

    /* 时间线：悬停提示 + 点击打开 */
    var tl = $('#timeline-host');
    tl.addEventListener('mousemove', function (e) {
      var dot = e.target.closest('.tl-dot');
      if (!dot) return;
      var title = dot.getAttribute('data-tip-title');
      if (title) {
        tooltipShow(title, dot.getAttribute('data-tip-sub'), e.clientX, e.clientY);
      }
    });
    tl.addEventListener('mouseover', function (e) {
      var dot = e.target.closest('.tl-dot');
      if (!dot) return;
      var title = dot.getAttribute('data-tip-title');
      if (title) tooltipShow(title, dot.getAttribute('data-tip-sub'), e.clientX, e.clientY);
    });
    tl.addEventListener('mouseout', function (e) {
      if (e.target.closest('.tl-dot')) tooltipHide();
    });
    tl.addEventListener('click', function (e) {
      var dot = e.target.closest('.tl-dot');
      if (dot) openDrawer(dot.getAttribute('data-id'));
    });

    /* 抽屉：编辑、chip、笔记模式、还原、复制 */
    var dbody = $('#drawer-body');
    dbody.addEventListener('change', function (e) {
      if (e.target.tagName === 'SELECT' && !e.target.hasAttribute('data-link')) applyEdit(e.target);
    });
    dbody.addEventListener('input', function (e) {
      if (e.target.hasAttribute('data-link')) { applyLinkInput(e.target); return; }
      if (e.target.tagName !== 'SELECT') applyEdit(e.target);
    });
    dbody.addEventListener('focusout', function (e) {
      if (e.target.hasAttribute('data-link')) blurLinkInput(e.target);
    });
    dbody.addEventListener('click', function (e) {
      var chip = e.target.closest('.chip[data-toggle]');
      if (chip) { togglePaperChip(chip); return; }
      var nm = e.target.closest('[data-note-mode]');
      if (nm) {
        state.noteMode = nm.getAttribute('data-note-mode');
        renderDrawer();
        return;
      }
      var lo = e.target.closest('[data-link-open]');
      if (lo) {
        var pl = getPaper(state.openId);
        if (pl) openLinkField(pl, lo.getAttribute('data-link-open'));
        return;
      }
      var lc = e.target.closest('[data-link-copy]');
      if (lc) {
        var pc = getPaper(state.openId);
        if (pc) copyLinkField(pc, lc.getAttribute('data-link-copy'));
        return;
      }
      var act = e.target.closest('[data-drawer-act]');
      if (!act) return;
      var a = act.getAttribute('data-drawer-act');
      var p = getPaper(state.openId);
      if (!p) return;
      if (a === 'copy-title') copyText(p.title, '已复制英文题名');
      else if (a === 'revert') revertPaper(state.openId);
      else if (a === 'delete') confirmDelete(state.openId);
    });

    $('#drawer-close').addEventListener('click', closeDrawer);
    $('#backdrop').addEventListener('click', closeDrawer);

    /* 顶栏：导出菜单 / 复制链接 / 主题 */
    var menuBtn = $('#export-btn');
    var menu = $('#export-menu');
    menuBtn.addEventListener('click', function (e) {
      e.stopPropagation();
      openMenu(menu.hidden);
    });
    document.addEventListener('click', function (e) {
      if (!e.target.closest('.menu-wrap')) openMenu(false);
    });
    menu.addEventListener('click', function (e) {
      var item = e.target.closest('.menu-item');
      if (!item) return;
      openMenu(false);
      var a = item.getAttribute('data-act');
      if (a === 'json') exportJSON();
      else if (a === 'csv') exportCSV();
      else if (a === 'md') exportMD();
      else if (a === 'offline') exportOffline();
      else if (a === 'print') window.print();
      else if (a === 'reload') confirmReload();
    });

    $('#copy-link').addEventListener('click', function () {
      copyText(location.href, '已复制当前视图链接（含全部筛选条件）');
    });
    $('#theme-btn').addEventListener('click', function () {
      var order = ['auto', 'light', 'dark'];
      setTheme(order[(order.indexOf(state.theme) + 1) % order.length]);
    });

    /* 空状态里的“清空筛选 / 清空搜索” */
    document.addEventListener('click', function (e) {
      var act = e.target.closest('[data-act]');
      if (!act) return;
      var a = act.getAttribute('data-act');
      if (a === 'clear-filters') clearFilters();
      else if (a === 'clear-search') {
        state.q = '';
        syncSearchInput();
        render();
      }
    });

    /* 键盘 */
    document.addEventListener('keydown', function (e) {
      if (e.key === 'Escape') {
        if (!$('#modal').hidden) { requestModalEscape(); return; }
        if (state.openId) { closeDrawer(); return; }
        openMenu(false);
        tooltipHide();
        return;
      }
      var tag = (e.target.tagName || '').toLowerCase();
      var typing = tag === 'input' || tag === 'textarea' || tag === 'select' || e.target.isContentEditable;
      if (e.metaKey || e.ctrlKey || e.altKey) return;
      if (e.key === '/' && !typing) {
        e.preventDefault();
        search.focus();
        search.select();
        return;
      }
      if (!typing && '1234'.indexOf(e.key) >= 0) {
        state.view = ['list', 'board', 'matrix', 'timeline'][Number(e.key) - 1];
        render();
        return;
      }
      if (!typing && (e.key === 'n' || e.key === 'N')) {
        if ($('#modal').hidden) {
          e.preventDefault();
          openAddPaperModal();
        }
        return;
      }
      if (e.key === 'Delete' && !typing && state.view === 'list' && !state.openId) {
        var did = state.selectedId;
        if (did && getPaper(did)) {
          e.preventDefault();
          confirmDelete(did);
        }
      }
    });

    /* 缩放：时间线重绘 */
    window.addEventListener('resize', debounce(function () {
      if (state.view === 'timeline') renderTimeline(filtered());
    }, 150));

    /* URL hash 变化（手动改地址栏 / 前进后退） */
    window.addEventListener('hashchange', function () {
      if (location.hash === lastHash) return;
      parseHash();
      syncSearchInput();
      if (state.openId && !getPaper(state.openId)) closeDrawer();
      render();
    });
  }

  /* --------------------------------------------------------------- 启动 */

  async function boot() {
    initTheme();
    state.readLabel = readLabelPref();
    document.body.classList.toggle('show-read-labels', state.readLabel);
    bindEvents();

    var loaded;
    try {
      loaded = await loadData();
    } catch (err) {
      var msg = (err && err.message) ? err.message : String(err);
      $('#source-note').textContent = '数据加载失败';
      $('#list-host').innerHTML = '<div class="empty">' +
        '<div class="empty-title">数据加载失败</div>' +
        '<div class="empty-sub">' + esc(msg) + '。请确认 data/papers.json 或 data/papers.offline.js 存在。</div></div>';
      toast('数据加载失败，请检查 data/ 目录');
      return;
    }

    state.dataSource = loaded.source;
    applyData(loaded.json);

    parseHash();
    syncSearchInput();
    buildVenueOptions();

    var dra = readDraft();
    if (dra) {
      var draftPapers = (dra.papers || []).map(function (raw, i) { return normalizePaper(raw, i); });
      var n = diffCount(draftPapers, normalizeOverrides(dra.matrix_overrides), state.baseline, state.baseOverrides);
      if (n > 0) {
        mergeDraft(dra);
        state.dirtyCount = computeDirtyCount();
        render();
        promptDraft(dra, n);
        return;
      }
      clearDraft();
    }

    state.dirtyCount = computeDirtyCount();
    render();
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }

})();