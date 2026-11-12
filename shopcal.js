/*
 * ShopCal — shared scheduling engine for TimberTrack and the Shop Calendar.
 *
 * Firestore:
 *   cal_settings/main   shop hours, breaks, moulder speeds, changeover, strapping
 *   cal_runs/{id}       a profile run: { id, profile, start "YYYY-MM-DDTHH:MM",
 *                       changeoverMin, entries: [ { id, poId, customer, profile,
 *                       lines: [...], lf, bf, minutes, addedAt } ] }
 *
 * A run's length = changeover + the minutes of every entry in it.
 * Time only counts inside shop hours (work days, start/end, minus breaks).
 */
(function (global) {
  'use strict';

  var FT_PER_M = 3.28084;
  var STANDARD_PROFILES = ['D4S', 'D3S', 'V Match', 'Sq Edge T&G', 'Shiplap', 'Channel Lap Shiplap', 'Cove'];
  var STANDARD_WIDTHS = [6, 8, 10, 12];

  var DEFAULT_SETTINGS = {
    workDays: [1, 2, 3, 4, 5],            // 0 = Sunday
    dayStart: '08:00',
    dayEnd: '17:00',
    breaks: [
      { start: '10:00', end: '10:15' },
      { start: '12:00', end: '13:00' },
      { start: '15:00', end: '15:15' }
    ],
    speedHz: { '6': null, '8': null, '10': null, '12': null },
    calHz: null,                           // a measured VFD setting...
    calMpm: null,                          // ...and the meters/minute it gave
    changeoverMin: 60,
    strapMin: 5,
    bfPerLift: 1000
  };

  var PROFILE_COLORS = {
    'D4S': 'slate', 'D3S': 'stone', 'V Match': 'amber', 'Sq Edge T&G': 'orange',
    'Shiplap': 'sky', 'Channel Lap Shiplap': 'teal', 'Cove': 'violet'
  };
  var COLOR_CLASSES = {
    slate:  { block: 'bg-slate-100 border-slate-400 text-slate-900',  dot: 'bg-slate-500' },
    stone:  { block: 'bg-stone-100 border-stone-400 text-stone-900',  dot: 'bg-stone-500' },
    amber:  { block: 'bg-amber-100 border-amber-500 text-amber-900',  dot: 'bg-amber-500' },
    orange: { block: 'bg-orange-100 border-orange-400 text-orange-900', dot: 'bg-orange-500' },
    sky:    { block: 'bg-sky-100 border-sky-500 text-sky-900',        dot: 'bg-sky-500' },
    teal:   { block: 'bg-teal-100 border-teal-500 text-teal-900',     dot: 'bg-teal-500' },
    violet: { block: 'bg-violet-100 border-violet-400 text-violet-900', dot: 'bg-violet-500' },
    rose:   { block: 'bg-rose-100 border-rose-400 text-rose-900',     dot: 'bg-rose-500' }
  };

  var db = null;
  var settings = clone(DEFAULT_SETTINGS);
  var runs = [];
  var listeners = [];
  var ready = { settings: false, runs: false };

  function clone(o) { return JSON.parse(JSON.stringify(o)); }
  function pad(n) { return (n < 10 ? '0' : '') + n; }
  function esc(str) {
    return String(str == null ? '' : str).replace(/[&<>"']/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c];
    });
  }

  /* ---------------- time helpers ---------------- */

  function hm(str) { var p = String(str || '0:0').split(':'); return (parseInt(p[0], 10) || 0) * 60 + (parseInt(p[1], 10) || 0); }
  function toLocalStr(d) { return d.getFullYear() + '-' + pad(d.getMonth() + 1) + '-' + pad(d.getDate()) + 'T' + pad(d.getHours()) + ':' + pad(d.getMinutes()); }
  function parseLocal(str) {
    var m = /^(\d{4})-(\d{2})-(\d{2})(?:T(\d{2}):(\d{2}))?/.exec(str || '');
    if (!m) return null;
    return new Date(+m[1], +m[2] - 1, +m[3], m[4] ? +m[4] : 0, m[5] ? +m[5] : 0, 0, 0);
  }
  function dateKey(d) { return d.getFullYear() + '-' + pad(d.getMonth() + 1) + '-' + pad(d.getDate()); }
  function minuteOfDay(d) { return d.getHours() * 60 + d.getMinutes(); }
  function atMinute(day, min) { return new Date(day.getFullYear(), day.getMonth(), day.getDate(), Math.floor(min / 60), min % 60, 0, 0); }
  function addDays(d, n) { return new Date(d.getFullYear(), d.getMonth(), d.getDate() + n); }

  function isWorkDay(d) { return settings.workDays.indexOf(d.getDay()) !== -1; }

  // Working segments of one day, as [startMin, endMin] pairs with breaks cut out.
  function daySegments(d) {
    if (!isWorkDay(d)) return [];
    var segs = [[hm(settings.dayStart), hm(settings.dayEnd)]];
    (settings.breaks || []).slice().sort(function (a, b) { return hm(a.start) - hm(b.start); }).forEach(function (br) {
      var bs = hm(br.start), be = hm(br.end), out = [];
      segs.forEach(function (s) {
        if (be <= s[0] || bs >= s[1]) { out.push(s); return; }
        if (bs > s[0]) out.push([s[0], bs]);
        if (be < s[1]) out.push([be, s[1]]);
      });
      segs = out;
    });
    return segs;
  }
  function workMinutesPerDay() {
    var d = new Date(2026, 0, 5); // a Monday
    for (var i = 0; i < 7 && !isWorkDay(d); i++) d = addDays(d, 1);
    return daySegments(d).reduce(function (a, s) { return a + s[1] - s[0]; }, 0);
  }

  // First moment at or after d that is inside shop hours.
  function nextWorkMoment(d) {
    var day = new Date(d.getFullYear(), d.getMonth(), d.getDate());
    var min = minuteOfDay(d);
    for (var i = 0; i < 370; i++) {
      var segs = daySegments(day);
      for (var j = 0; j < segs.length; j++) {
        if (min < segs[j][1]) return atMinute(day, Math.max(min, segs[j][0]));
      }
      day = addDays(day, 1); min = 0;
    }
    return d;
  }

  // Walk forward through shop hours. Returns the moment the work ends.
  function addWorkMinutes(start, minutes) {
    var cur = nextWorkMoment(start);
    var left = Math.max(0, Math.round(minutes));
    if (left === 0) return cur;
    var day = new Date(cur.getFullYear(), cur.getMonth(), cur.getDate());
    var min = minuteOfDay(cur);
    for (var i = 0; i < 2000; i++) {
      var segs = daySegments(day);
      for (var j = 0; j < segs.length; j++) {
        var s = Math.max(segs[j][0], min), e = segs[j][1];
        if (s >= e) continue;
        if (e - s >= left) return atMinute(day, s + left);
        left -= (e - s);
      }
      day = addDays(day, 1); min = 0;
    }
    return cur;
  }

  // Shop minutes between two moments (0 if b <= a).
  function workMinutesBetween(a, b) {
    if (b <= a) return 0;
    var total = 0, day = new Date(a.getFullYear(), a.getMonth(), a.getDate());
    var endDay = new Date(b.getFullYear(), b.getMonth(), b.getDate());
    for (var i = 0; i < 2000 && day <= endDay; i++) {
      daySegments(day).forEach(function (seg) {
        var s = atMinute(day, seg[0]), e = atMinute(day, seg[1]);
        var lo = s < a ? a : s, hi = e > b ? b : e;
        if (hi > lo) total += (hi - lo) / 60000;
      });
      day = addDays(day, 1);
    }
    return Math.round(total);
  }

  /* ---------------- speeds and estimates ---------------- */

  function hzToMpm(hz) {
    hz = parseFloat(hz);
    if (!(hz > 0) || !(settings.calHz > 0) || !(settings.calMpm > 0)) return null;
    return hz * settings.calMpm / settings.calHz;
  }
  function speedForWidth(w) {
    return hzToMpm(settings.speedHz && settings.speedHz[String(w)]);
  }

  function lineProfile(it) { return it.targetProfile || it.sourceStage || 'Rough'; }
  function isMouldedLine(it) { return lineProfile(it) !== 'Rough'; }

  function isStandardLine(it) {
    return STANDARD_PROFILES.indexOf(lineProfile(it)) !== -1 &&
      parseFloat(it.thickness) === 1 &&
      STANDARD_WIDTHS.indexOf(parseFloat(it.width)) !== -1;
  }

  function lineLF(it) {
    var t = parseFloat(it.thickness) || 0, w = parseFloat(it.width) || 0, l = parseFloat(it.length) || 0;
    var pcs = parseFloat(it.pieces) || 0;
    if (it.bfOnly) {
      if (t > 0 && w > 0) return (parseFloat(it.bf) || pcs) * 12 / (t * w);
      return null;
    }
    if (l > 0) return pcs * l;
    var bf = parseFloat(it.bf) || 0;
    if (bf > 0 && t > 0 && w > 0) return bf * 12 / (t * w);
    return null;
  }

  function strapMinutes(bf) {
    var lifts = Math.max(1, Math.floor((parseFloat(bf) || 0) / (settings.bfPerLift || 1000)));
    return lifts * (settings.strapMin || 0);
  }

  function feedMinutes(lf, mpm) {
    if (!(lf > 0) || !(mpm > 0)) return null;
    return (lf / FT_PER_M) / mpm;
  }

  function fmtDur(min) {
    min = Math.round(min || 0);
    var h = Math.floor(min / 60), m = min % 60;
    if (!h) return m + ' min';
    return h + ' h' + (m ? ' ' + m + ' min' : '');
  }
  function fmtTime(d) {
    var h = d.getHours(), m = d.getMinutes();
    return ((h + 11) % 12 + 1) + ':' + pad(m) + (h < 12 ? ' am' : ' pm');
  }
  var DOW = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'];
  var MON = ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec'];
  function fmtDay(d) { return DOW[d.getDay()] + ' ' + MON[d.getMonth()] + ' ' + d.getDate(); }
  function fmtWhen(d) { return fmtDay(d) + ', ' + fmtTime(d); }

  /* ---------------- runs ---------------- */

  function runStart(r) { return nextWorkMoment(parseLocal(r.start)); }
  function runMinutes(r) {
    return (parseFloat(r.changeoverMin) || 0) + (r.entries || []).reduce(function (a, e) { return a + (parseFloat(e.minutes) || 0); }, 0);
  }
  function runEnd(r) { return addWorkMinutes(runStart(r), runMinutes(r)); }
  function sortRuns(list) { return list.slice().sort(function (a, b) { return parseLocal(a.start) - parseLocal(b.start); }); }
  function colorFor(profile) { return COLOR_CLASSES[PROFILE_COLORS[profile] || 'rose']; }

  // Push later runs back only as far as needed, starting after `fromId`.
  // Returns [{ id, profile, from, to }] for every run that moves. Mutates `list`.
  function rippleFrom(list, fromId) {
    var sorted = sortRuns(list);
    var idx = sorted.findIndex(function (r) { return r.id === fromId; });
    var moves = [];
    if (idx === -1) return moves;
    var prevEnd = runEnd(sorted[idx]);
    for (var i = idx + 1; i < sorted.length; i++) {
      var r = sorted[i];
      var st = runStart(r);
      if (st >= prevEnd) break;
      var newStart = nextWorkMoment(prevEnd);
      moves.push({ id: r.id, profile: r.profile, from: st, to: newStart });
      r.start = toLocalStr(newStart);
      prevEnd = runEnd(r);
    }
    return moves;
  }

  // Runs that overlap the run before them (for red warnings).
  function overlapIds(list) {
    var ids = {}, sorted = sortRuns(list);
    for (var i = 1; i < sorted.length; i++) {
      if (runStart(sorted[i]) < runEnd(sorted[i - 1])) { ids[sorted[i].id] = true; ids[sorted[i - 1].id] = true; }
    }
    return ids;
  }

  function dueMoment(dueDate) {
    var d = parseLocal(dueDate);
    if (!d) return null;
    return atMinute(d, hm(settings.dayEnd));
  }

  // Entries that would finish after their PO's due date.
  function lateEntries(list, poLookup) {
    var out = [];
    list.forEach(function (r) {
      var end = runEnd(r);
      (r.entries || []).forEach(function (e) {
        var po = poLookup ? poLookup(e.poId) : null;
        var due = dueMoment(po ? po.dueDate : e.dueDate);
        if (due && end > due) out.push({ run: r, entry: e, due: due, end: end });
      });
    });
    return out;
  }

  // Earliest time from `from` where `minutes` fit between existing runs.
  function firstOpenSlot(list, minutes, from) {
    var t = nextWorkMoment(from || new Date());
    var sorted = sortRuns(list);
    for (var i = 0; i < sorted.length; i++) {
      var s = runStart(sorted[i]), e = runEnd(sorted[i]);
      if (e <= t) continue;
      if (addWorkMinutes(t, minutes) <= s) return t;
      if (e > t) t = nextWorkMoment(e);
    }
    return t;
  }

  /* ---------------- Firestore ---------------- */

  function notify() { listeners.forEach(function (fn) { try { fn(); } catch (e) {} }); }

  function init(firestore) {
    db = firestore;
    if (!db) return;
    db.collection('cal_settings').doc('main').onSnapshot(function (doc) {
      var data = doc.exists ? doc.data() : {};
      settings = Object.assign(clone(DEFAULT_SETTINGS), data || {});
      settings.speedHz = Object.assign(clone(DEFAULT_SETTINGS.speedHz), (data && data.speedHz) || {});
      ready.settings = true;
      notify();
    }, function () { ready.settings = true; notify(); });
    db.collection('cal_runs').onSnapshot(function (snap) {
      var list = [];
      snap.forEach(function (doc) { list.push(doc.data()); });
      runs = list;
      ready.runs = true;
      notify();
    }, function () { ready.runs = true; notify(); });
  }

  function saveSettings(newSettings) {
    settings = Object.assign(clone(DEFAULT_SETTINGS), newSettings);
    notify();
    if (db) return db.collection('cal_settings').doc('main').set(clone(settings));
    return Promise.resolve();
  }

  function saveRuns(list) {
    var byId = {};
    list.forEach(function (r) { byId[r.id] = r; });
    runs = runs.filter(function (r) { return !byId[r.id]; }).concat(list.map(clone));
    notify();
    if (!db) return Promise.resolve();
    var batch = db.batch();
    list.forEach(function (r) { batch.set(db.collection('cal_runs').doc(r.id), clone(r)); });
    return batch.commit();
  }

  function deleteRun(id) {
    runs = runs.filter(function (r) { return r.id !== id; });
    notify();
    if (db) return db.collection('cal_runs').doc(id).delete();
    return Promise.resolve();
  }

  function newId(prefix) { return prefix + '-' + Date.now().toString(36) + Math.floor(Math.random() * 1e5).toString(36); }

  // Take a PO off the calendar (used when a PO is deleted in TimberTrack).
  function removePoEntries(poId) {
    var changed = [];
    runs.forEach(function (r) {
      if ((r.entries || []).some(function (e) { return e.poId === poId; })) {
        var c = clone(r);
        c.entries = c.entries.filter(function (e) { return e.poId !== poId; });
        changed.push(c);
      }
    });
    return changed.length ? saveRuns(changed) : Promise.resolve();
  }

  function entriesForPo(poId) {
    var out = [];
    runs.forEach(function (r) { (r.entries || []).forEach(function (e) { if (e.poId === poId) out.push({ run: r, entry: e }); }); });
    return out;
  }

  /* ---------------- prompt UI ---------------- */

  var BTN = {
    primary: 'bg-sky-600 hover:bg-sky-700 text-white',
    amber: 'bg-amber-500 hover:bg-amber-600 text-white',
    plain: 'bg-slate-100 hover:bg-slate-200 text-slate-700 border border-slate-300',
    danger: 'bg-rose-600 hover:bg-rose-700 text-white',
    ghost: 'bg-white hover:bg-slate-50 text-slate-500 border border-slate-200'
  };

  // Shows a dialog. buttons: [{ label, value, style }]. Resolves { value, form }.
  function ask(opts) {
    return new Promise(function (resolve) {
      var wrap = document.createElement('div');
      wrap.className = 'shopcal-dialog';
      wrap.style.cssText = 'position:fixed;inset:0;z-index:10050;background:rgba(15,23,42,0.6);display:flex;align-items:flex-end;justify-content:center;';
      wrap.innerHTML =
        '<div class="bg-white w-full sm:max-w-lg sm:mb-8 rounded-t-2xl sm:rounded-2xl shadow-2xl max-h-[92vh] flex flex-col">' +
          '<div class="px-4 pt-4 pb-2 border-b border-slate-100 flex items-start gap-2">' +
            '<span class="text-xl leading-none">📅</span>' +
            '<div class="min-w-0"><div class="text-sm font-black text-slate-900 uppercase tracking-wider">' + esc(opts.title || 'Shop Calendar') + '</div>' +
            (opts.subtitle ? '<div class="text-xs text-slate-500 mt-0.5">' + opts.subtitle + '</div>' : '') + '</div>' +
          '</div>' +
          '<form class="px-4 py-3 overflow-y-auto text-sm text-slate-800 space-y-3" onsubmit="return false">' + (opts.body || '') + '</form>' +
          '<div class="px-4 pb-4 pt-2 grid gap-2">' +
            (opts.buttons || []).map(function (b, i) {
              return '<button type="button" data-i="' + i + '" class="w-full py-3 rounded-xl font-bold text-sm active:scale-[0.98] ' + (BTN[b.style || 'plain']) + '">' + b.label + '</button>';
            }).join('') +
          '</div>' +
        '</div>';
      document.body.appendChild(wrap);
      var form = wrap.querySelector('form');
      var errBox = null;
      wrap.querySelectorAll('button[data-i]').forEach(function (btn) {
        btn.addEventListener('click', function () {
          var b = opts.buttons[+btn.getAttribute('data-i')];
          if (b.validate) {
            var err = b.validate(form);
            if (err) {
              if (!errBox) { errBox = document.createElement('div'); errBox.className = 'text-xs font-bold text-rose-700 bg-rose-50 border border-rose-200 rounded-lg px-3 py-2'; form.appendChild(errBox); }
              errBox.innerText = err;
              return;
            }
          }
          var values = {};
          form.querySelectorAll('[name]').forEach(function (el) {
            values[el.name] = el.type === 'checkbox' ? el.checked : (el.type === 'radio' ? (el.checked ? el.value : values[el.name]) : el.value);
          });
          wrap.remove();
          resolve({ value: b.value, form: values });
        });
      });
      if (opts.onOpen) opts.onOpen(form);
    });
  }

  function toast(msg) {
    document.querySelectorAll('.shopcal-toast').forEach(function (el) { el.remove(); });
    var t = document.createElement('div');
    t.style.cssText = 'position:fixed;left:50%;bottom:24px;transform:translateX(-50%);z-index:10060;max-width:92vw;';
    t.className = 'shopcal-toast px-4 py-2.5 rounded-xl bg-slate-900 text-white text-sm font-bold shadow-xl';
    t.innerText = msg;
    document.body.appendChild(t);
    setTimeout(function () { t.remove(); }, 3200);
  }

  var INPUT = 'w-full bg-slate-50 border border-slate-300 rounded-xl px-3 py-2 text-sm font-mono font-bold text-slate-800 focus:outline-none focus:border-amber-500';

  function lineDesc(it) {
    var dim = it.thickness + '"×' + (parseFloat(it.width) === 0 ? 'RW' : it.width + '"') + '×' + (parseFloat(it.length) === 0 ? 'RL' : it.length + "'");
    var qty = it.bfOnly ? (it.pieces + ' BF') : (it.pieces + ' pcs');
    return qty + ' ' + dim + ' ' + lineProfile(it);
  }

  // Works out feed minutes for one line, asking for a speed when needed.
  function estimateLine(it, poId) {
    var lf = lineLF(it);
    var bf = parseFloat(it.bf) || 0;
    var w = parseFloat(it.width);
    var standard = isStandardLine(it);
    var mpm = standard ? speedForWidth(w) : null;
    if (lf && mpm) return Promise.resolve({ lf: lf, bf: bf, feed: feedMinutes(lf, mpm), mpm: mpm });

    var calibrated = settings.calHz > 0 && settings.calMpm > 0;
    var why = !standard ? 'Custom job — what speed will the moulder run?' :
      (!lf ? "This line has random lengths/widths, so the feet can't be worked out." : 'No moulder speed is saved for ' + w + '" yet.');
    var body =
      '<div class="rounded-xl bg-slate-50 border border-slate-200 px-3 py-2"><div class="font-bold">' + esc(lineDesc(it)) + '</div>' +
      '<div class="text-xs text-slate-500">PO ' + esc(poId) + (lf ? ' • ' + Math.round(lf).toLocaleString() + ' linear ft' : '') + '</div></div>' +
      '<div class="text-sm font-bold text-amber-800">' + esc(why) + '</div>';
    if (lf) {
      body += calibrated ?
        '<label class="block text-xs font-bold text-slate-600 uppercase">VFD setting (Hz)<input name="hz" type="number" step="0.1" inputmode="decimal" class="' + INPUT + ' mt-1" placeholder="e.g. 40" /></label>' +
        '<div class="text-xs text-slate-500" data-mpm-out></div>' :
        '<label class="block text-xs font-bold text-slate-600 uppercase">Moulder speed (meters per minute)<input name="mpm" type="number" step="0.1" inputmode="decimal" class="' + INPUT + ' mt-1" placeholder="e.g. 12" /></label>';
      if (standard) body += '<label class="flex items-center gap-2 text-xs font-bold text-slate-600"><input name="saveDefault" type="checkbox" class="w-4 h-4" checked /> Save as the ' + w + '" speed for next time</label>';
      body += '<div class="text-xs text-slate-400">— or —</div>';
    }
    body += '<label class="block text-xs font-bold text-slate-600 uppercase">Enter the moulding time instead (minutes)<input name="manual" type="number" step="1" inputmode="numeric" class="' + INPUT + ' mt-1" placeholder="e.g. 90" /></label>';

    return ask({
      title: 'Moulder speed needed',
      body: body,
      onOpen: function (form) {
        var hz = form.querySelector('[name=hz]'), out = form.querySelector('[data-mpm-out]');
        if (hz && out) hz.addEventListener('input', function () { var m = hzToMpm(hz.value); out.innerText = m ? '= ' + m.toFixed(1) + ' m/min (' + (m * FT_PER_M).toFixed(1) + ' ft/min)' : ''; });
      },
      buttons: [
        { label: 'Use this', value: 'ok', style: 'primary', validate: function (form) {
          var g = function (n) { var el = form.querySelector('[name=' + n + ']'); return el ? parseFloat(el.value) : NaN; };
          if (g('manual') > 0 || g('hz') > 0 || g('mpm') > 0) return null;
          return 'Enter a speed or a time.';
        } },
        { label: 'Skip this line', value: 'skipline', style: 'ghost' }
      ]
    }).then(function (res) {
      if (res.value !== 'ok') return null;
      var f = res.form;
      if (parseFloat(f.manual) > 0) return { lf: lf || 0, bf: bf, feed: parseFloat(f.manual), mpm: null, manual: true };
      var m = parseFloat(f.mpm) > 0 ? parseFloat(f.mpm) : hzToMpm(f.hz);
      if (standard && f.saveDefault && lf) {
        var s = clone(settings);
        if (parseFloat(f.hz) > 0) { s.speedHz[String(w)] = parseFloat(f.hz); saveSettings(s); }
      }
      return { lf: lf, bf: bf, feed: feedMinutes(lf, m), mpm: m };
    });
  }

  function estimateGroup(lines, poId) {
    var results = [];
    return lines.reduce(function (p, it) {
      return p.then(function () { return estimateLine(it, poId).then(function (r) { if (r) results.push({ line: it, est: r }); }); });
    }, Promise.resolve()).then(function () {
      if (!results.length) return null;
      var lf = 0, bf = 0, feed = 0;
      results.forEach(function (r) { lf += r.est.lf || 0; bf += r.est.bf || 0; feed += r.est.feed || 0; });
      var strap = strapMinutes(bf);
      return { lines: results, lf: lf, bf: bf, feed: feed, strap: strap, total: Math.ceil(feed + strap) };
    });
  }

  function runLabel(r) { return '<b>' + esc(r.profile) + '</b> run — ' + fmtWhen(runStart(r)) + ' to ' + fmtTime(runEnd(r)) + (dateKey(runStart(r)) !== dateKey(runEnd(r)) ? ' ' + fmtDay(runEnd(r)) : ''); }

  // Places one group (one profile) of a PO on the calendar.
  function placeGroup(po, profile, group) {
    var now = new Date();
    var upcoming = sortRuns(runs).filter(function (r) { return r.profile === profile && runEnd(r) > now; });
    var due = dueMoment(po.dueDate);
    var suggestAt = firstOpenSlot(runs, group.total + (settings.changeoverMin || 0), now);

    var body =
      '<div class="rounded-xl bg-slate-50 border border-slate-200 px-3 py-2 space-y-0.5">' +
        '<div class="font-black">' + esc(po.customer) + ' <span class="font-mono text-xs text-sky-800">' + esc(po.id) + '</span></div>' +
        group.lines.map(function (l) { return '<div class="text-xs text-slate-600">• ' + esc(lineDesc(l.line)) + '</div>'; }).join('') +
        '<div class="text-xs text-slate-500">' + Math.round(group.lf).toLocaleString() + ' LF • ' + Math.round(group.bf).toLocaleString() + ' BF' + (po.dueDate ? ' • <b class="text-amber-800">Due ' + fmtDay(parseLocal(po.dueDate)) + '</b>' : '') + '</div>' +
      '</div>' +
      '<div class="grid grid-cols-2 gap-2 text-xs">' +
        '<div class="rounded-lg border border-slate-200 px-2 py-1.5">Moulding<br><b class="text-sm">' + fmtDur(group.feed) + '</b></div>' +
        '<div class="rounded-lg border border-slate-200 px-2 py-1.5">Strapping<br><b class="text-sm">' + fmtDur(group.strap) + '</b></div>' +
      '</div>' +
      '<label class="block text-xs font-bold text-slate-600 uppercase">Time to book (minutes) — change it if it looks off' +
        '<input name="minutes" type="number" step="5" inputmode="numeric" value="' + group.total + '" class="' + INPUT + ' mt-1" /></label>' +
      '<div class="text-xs font-bold text-slate-600 uppercase pt-1">Where should it go?</div>' +
      '<div class="space-y-2">' +
        upcoming.slice(0, 5).map(function (r, i) {
          return '<label class="flex items-start gap-2 rounded-xl border border-slate-200 px-3 py-2 has-[:checked]:border-sky-500 has-[:checked]:bg-sky-50">' +
            '<input type="radio" name="target" value="' + r.id + '"' + (i === 0 ? ' checked' : '') + ' class="mt-1 w-4 h-4" />' +
            '<span class="text-sm">' + (i === 0 ? 'Next ' : '') + runLabel(r) + '<br><span class="text-xs text-slate-500">' + (r.entries || []).length + ' order(s) in it</span></span></label>';
        }).join('') +
        '<label class="flex items-start gap-2 rounded-xl border border-slate-200 px-3 py-2 has-[:checked]:border-amber-500 has-[:checked]:bg-amber-50">' +
          '<input type="radio" name="target" value="NEW"' + (upcoming.length ? '' : ' checked') + ' class="mt-1 w-4 h-4" />' +
          '<span class="flex-1 text-sm">New <b>' + esc(profile) + '</b> run starting:' +
          '<input name="newStart" type="datetime-local" value="' + toLocalStr(suggestAt) + '" class="' + INPUT + ' mt-1" />' +
          '<span class="text-xs text-slate-500">Includes ' + fmtDur(settings.changeoverMin) + ' changeover. Suggested: next open time.</span></span></label>' +
      '</div>' +
      (!upcoming.length ? '<div class="text-xs text-slate-500">There are no ' + esc(profile) + ' runs coming up.</div>' : '');

    return ask({
      title: 'Put ' + profile + ' on the calendar?',
      subtitle: 'PO ' + esc(po.id),
      body: body,
      buttons: [
        { label: 'Add to calendar', value: 'add', style: 'primary', validate: function (form) {
          var m = parseFloat(form.querySelector('[name=minutes]').value);
          if (!(m > 0)) return 'Enter the time to book.';
          var t = form.querySelector('[name=target]:checked');
          if (!t) return 'Pick a run or a new run.';
          if (t.value === 'NEW' && !form.querySelector('[name=newStart]').value) return 'Pick a start date and time.';
          return null;
        } },
        { label: 'Skip — don’t put this on the calendar', value: 'skip', style: 'ghost' }
      ]
    }).then(function (res) {
      if (res.value !== 'add') return 'skipped';
      var minutes = Math.round(parseFloat(res.form.minutes));
      var entry = {
        id: newId('E'), poId: po.id, customer: po.customer || '', profile: profile, dueDate: po.dueDate || '',
        lines: group.lines.map(function (l) { return { desc: lineDesc(l.line), lf: Math.round(l.est.lf || 0), bf: Math.round(l.est.bf || 0), mpm: l.est.mpm ? +l.est.mpm.toFixed(2) : null }; }),
        lf: Math.round(group.lf), bf: Math.round(group.bf), minutes: minutes, estMinutes: group.total, addedAt: Date.now()
      };
      var draft = clone(runs);
      var target;
      if (res.form.target === 'NEW') {
        var st = nextWorkMoment(parseLocal(res.form.newStart));
        var inside = sortRuns(draft).find(function (r) { return runStart(r) <= st && runEnd(r) > st; });
        if (inside) {
          return ask({ title: 'That time is taken', body: 'The ' + runLabel(inside) + ' is already booked then.<br>Start the new run when it finishes, at <b>' + fmtWhen(runEnd(inside)) + '</b>?',
            buttons: [{ label: 'Yes, start it then', value: 'yes', style: 'primary' }, { label: 'Cancel', value: 'no', style: 'ghost' }] })
            .then(function (r2) {
              if (r2.value !== 'yes') return 'skipped';
              return commitNew(draft, profile, nextWorkMoment(runEnd(inside)), entry, po);
            });
        }
        return commitNew(draft, profile, st, entry, po);
      }
      target = draft.find(function (r) { return r.id === res.form.target; });
      target.entries = (target.entries || []).concat([entry]);
      return confirmAndSave(draft, target.id, [target.id], po, 'Added to the ' + profile + ' run on ' + fmtDay(runStart(target)) + '.');
    });
  }

  function commitNew(draft, profile, start, entry, po) {
    var run = { id: newId('RUN'), profile: profile, start: toLocalStr(start), changeoverMin: settings.changeoverMin || 0, entries: [entry], createdAt: Date.now() };
    draft.push(run);
    return confirmAndSave(draft, run.id, [run.id], po, 'New ' + profile + ' run booked for ' + fmtWhen(start) + '.');
  }

  // After a change to run `changedId`: if it now runs into the next run, ask before pushing.
  function confirmAndSave(draft, changedId, touchedIds, po, doneMsg) {
    var changed = draft.find(function (r) { return r.id === changedId; });
    var sorted = sortRuns(draft);
    var next = sorted[sorted.indexOf(changed) + 1];
    var overlap = next && runStart(next) < runEnd(changed);

    var finish = function (list, ids, extraMsg) {
      var late = lateEntries(list.filter(function (r) { return ids.indexOf(r.id) !== -1; }), poLookup);
      var save = function () {
        return saveRuns(list.filter(function (r) { return ids.indexOf(r.id) !== -1; })).then(function () { toast(doneMsg + (extraMsg || '')); return 'saved'; });
      };
      if (!late.length) return save();
      return ask({
        title: 'Due date warning',
        body: '<div class="text-rose-700 font-bold">These orders would be finished after their due date:</div>' +
          late.map(function (l) { return '<div class="text-sm">• <b>' + esc(l.entry.customer) + '</b> ' + esc(l.entry.poId) + ' — due ' + fmtDay(l.due) + ', done ' + fmtWhen(l.end) + '</div>'; }).join(''),
        buttons: [{ label: 'Save anyway', value: 'save', style: 'primary' }, { label: 'Cancel', value: 'cancel', style: 'ghost' }]
      }).then(function (r) { return r.value === 'save' ? save() : 'cancelled'; });
    };

    if (!overlap) return finish(draft, touchedIds);

    var pushed = clone(draft);
    var moves = rippleFrom(pushed, changedId);
    var over = workMinutesBetween(runStart(next), runEnd(changed));
    var body =
      '<div>This makes the <b>' + esc(changed.profile) + '</b> run end at <b>' + fmtWhen(runEnd(changed)) + '</b>, which runs ' + fmtDur(over) + ' into the <b>' + esc(next.profile) + '</b> run starting ' + fmtWhen(runStart(next)) + '.</div>' +
      '<div class="text-xs font-bold text-slate-600 uppercase pt-1">If you push, these move:</div>' +
      moves.map(function (m) { return '<div class="text-sm">• <b>' + esc(m.profile) + '</b>: ' + fmtWhen(m.from) + ' → <b>' + fmtWhen(m.to) + '</b></div>'; }).join('');
    return ask({
      title: 'Runs into the next run',
      body: body,
      buttons: [
        { label: 'Push ' + (moves.length === 1 ? 'the next run' : moves.length + ' runs') + ' back', value: 'push', style: 'primary' },
        { label: 'Add anyway (they will overlap)', value: 'overlap', style: 'plain' },
        { label: 'Cancel', value: 'cancel', style: 'ghost' }
      ]
    }).then(function (r) {
      if (r.value === 'push') return finish(pushed, touchedIds.concat(moves.map(function (m) { return m.id; })), moves.length ? ' Pushed ' + moves.length + ' run(s) back.' : '');
      if (r.value === 'overlap') return finish(draft, touchedIds, ' Runs overlap — shown in red.');
      return 'cancelled';
    });
  }

  var poLookup = null;
  function setPoLookup(fn) { poLookup = fn; }

  // Main entry: offer to put a PO's moulded lines on the calendar.
  function schedulePo(po, opts) {
    opts = opts || {};
    var lines = (po.items || []).filter(isMouldedLine);
    if (!lines.length) { if (opts.quietIfNone !== true) toast('Nothing to mould on this PO — all lines are Rough.'); return Promise.resolve('none'); }
    var already = entriesForPo(po.id);
    var pre = already.length && !opts.force ?
      ask({ title: 'Already on the calendar', body: 'PO ' + esc(po.id) + ' is already in ' + already.length + ' run(s):<br>' + already.map(function (a) { return '• ' + runLabel(a.run); }).join('<br>') + '<br><br>Add it again?',
        buttons: [{ label: 'Add again', value: 'go', style: 'primary' }, { label: 'Cancel', value: 'no', style: 'ghost' }] }) :
      Promise.resolve({ value: 'go' });

    return pre.then(function (r0) {
      if (r0.value !== 'go') return 'cancelled';
      var profiles = [];
      lines.forEach(function (l) { var p = lineProfile(l); if (profiles.indexOf(p) === -1) profiles.push(p); });

      var grouping = profiles.length < 2 ? Promise.resolve({ split: true }) :
        ask({
          title: 'Different profiles on this PO',
          subtitle: 'PO ' + esc(po.id) + ' — ' + profiles.map(esc).join(', '),
          body: '<div>Put each profile in its own run, or keep the whole order together in one run?</div>' +
            '<div class="space-y-1">' + lines.map(function (l) { return '<div class="text-xs text-slate-600">• ' + esc(lineDesc(l)) + '</div>'; }).join('') + '</div>' +
            '<label class="block text-xs font-bold text-slate-600 uppercase pt-1">If kept together, put it in the run for:' +
            '<select name="togetherProfile" class="' + INPUT + ' mt-1">' + profiles.map(function (p) { return '<option>' + esc(p) + '</option>'; }).join('') + '</select></label>',
          buttons: [
            { label: 'Split — each profile to its own run', value: 'split', style: 'primary' },
            { label: 'Keep together', value: 'together', style: 'amber' },
            { label: 'Skip — don’t put this on the calendar', value: 'skip', style: 'ghost' }
          ]
        }).then(function (r) { return r.value === 'skip' ? null : { split: r.value === 'split', profile: r.form.togetherProfile }; });

      return grouping.then(function (g) {
        if (!g) return 'skipped';
        var groups = g.split ?
          profiles.map(function (p) { return { profile: p, lines: lines.filter(function (l) { return lineProfile(l) === p; }) }; }) :
          [{ profile: g.profile, lines: lines }];
        var outcome = [];
        return groups.reduce(function (p, grp) {
          return p.then(function () {
            return estimateGroup(grp.lines, po.id).then(function (est) {
              if (!est) return;
              return placeGroup(po, grp.profile, est).then(function (o) { outcome.push(o); });
            });
          });
        }, Promise.resolve()).then(function () { return outcome; });
      });
    });
  }

  global.ShopCal = {
    init: init, onChange: function (fn) { listeners.push(fn); }, setPoLookup: setPoLookup,
    getSettings: function () { return settings; }, getRuns: function () { return runs; }, isReady: function () { return ready.settings && ready.runs; },
    saveSettings: saveSettings, saveRuns: saveRuns, deleteRun: deleteRun, schedulePo: schedulePo, entriesForPo: entriesForPo, removePoEntries: removePoEntries,
    confirmAndSave: confirmAndSave, rippleFrom: rippleFrom, overlapIds: overlapIds, lateEntries: lateEntries,
    runStart: runStart, runEnd: runEnd, runMinutes: runMinutes, sortRuns: sortRuns, firstOpenSlot: firstOpenSlot,
    daySegments: daySegments, workMinutesPerDay: workMinutesPerDay, addWorkMinutes: addWorkMinutes, nextWorkMoment: nextWorkMoment,
    workMinutesBetween: workMinutesBetween, hzToMpm: hzToMpm, speedForWidth: speedForWidth, strapMinutes: strapMinutes,
    feedMinutes: feedMinutes, lineLF: lineLF, isStandardLine: isStandardLine, lineProfile: lineProfile, isMouldedLine: isMouldedLine,
    parseLocal: parseLocal, toLocalStr: toLocalStr, dateKey: dateKey, hm: hm, dueMoment: dueMoment,
    fmtDur: fmtDur, fmtTime: fmtTime, fmtDay: fmtDay, fmtWhen: fmtWhen, colorFor: colorFor, esc: esc,
    ask: ask, toast: toast, newId: newId, clone: clone, FT_PER_M: FT_PER_M, STANDARD_PROFILES: STANDARD_PROFILES, DEFAULT_SETTINGS: DEFAULT_SETTINGS
  };
})(window);
