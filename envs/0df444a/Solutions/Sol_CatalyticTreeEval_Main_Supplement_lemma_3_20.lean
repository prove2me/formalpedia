-- Prove2me | solution 1 for CatalyticTreeEval.Main.Supplement.lemma_3_20
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T13:51:34.410215+00:00
-- url     : https://prove2.me/submissions/e6bcfaba-bf9d-463d-9d9f-4308345ff9af

import Definitions.Def_CatalyticTreeEval_Main_Decoder

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement
open CatalyticMatching.General

abbrev Cond := Option Bool → Bool → Bool → Bool → Bool

inductive Ins
  | act (w : Option Bool) (wm im : Move) (e : Option Bool)
  | br (c : Cond) (t : ℕ)
  | jmp (t : ℕ)

inductive Prog
  | act (w : Option Bool) (wm im : Move) (e : Option Bool)
  | skip
  | seq (p q : Prog)
  | ite (c : Cond) (p q : Prog)
  | while (c : Cond) (p : Prog)

def Prog.size : Prog → ℕ
  | .act .. => 1
  | .skip => 0
  | .seq p q => p.size + q.size
  | .ite _ p q => q.size + p.size + 2
  | .while _ p => p.size + 2

def Prog.comp : Prog → ℕ → List Ins
  | .act w wm im e, _ => [.act w wm im e]
  | .skip, _ => []
  | .seq p q, a => p.comp a ++ q.comp (a + p.size)
  | .ite c p q, a =>
      [.br c (a + 1 + q.size + 1)] ++ q.comp (a + 1) ++ [.jmp (a + q.size + p.size + 2)]
        ++ p.comp (a + q.size + 2)
  | .while c p, a =>
      [.br (fun x w i o => !c x w i o) (a + p.size + 2)] ++ p.comp (a + 1) ++ [.jmp a]

lemma Prog.comp_length (p : Prog) (a : ℕ) : (p.comp a).length = p.size := by
  induction p generalizing a <;> simp [Prog.comp, Prog.size, *] <;> omega

def Ins.instr (n : ℕ) (pc : ℕ) (i : Ins) (a : Option Bool) (w ie we : Bool) : Instruction n :=
  let nx : ℕ → Option (Fin n) := fun t => if h : t < n then some ⟨t, h⟩ else none
  match i with
  | .act wr wm im e => ⟨nx (pc + 1), wr.getD w, none, im, wm, .stay, e⟩
  | .br c t => ⟨nx (if c a w ie we then t else pc + 1), w, none, .stay, .stay, .stay, none⟩
  | .jmp t => ⟨nx t, w, none, .stay, .stay, .stay, none⟩

def toMachine (code : List Ins) : Machine where
  states := code.length + 1
  start := ⟨0, by omega⟩
  table := fun q a w _ ie we _ =>
    match code[q.val]? with
    | some i => i.instr (code.length + 1) q.val a w ie we
    | none => ⟨none, w, none, .stay, .stay, .stay, none⟩

structure St where
  ih : ℕ
  wh : ℕ
  work : ℕ → Bool
  out : List Bool

def St.sens (x : List Bool) (s : St) : Option Bool × Bool × Bool × Bool :=
  ((if s.ih = 0 then none else x[s.ih - 1]?), s.work s.wh, s.ih == 0, s.wh == 0)

def St.test (x : List Bool) (c : Cond) (s : St) : Bool :=
  c (if s.ih = 0 then none else x[s.ih - 1]?) (s.work s.wh) (s.ih == 0) (s.wh == 0)

def St.act (s : St) (w : Option Bool) (wm im : Move) (e : Option Bool) : St :=
  ⟨im.apply s.ih, wm.apply s.wh, Function.update s.work s.wh (w.getD (s.work s.wh)),
    s.out ++ e.toList⟩

/-- Big-step semantics; every visited work head stays below `B`. -/
inductive Eval (x : List Bool) (B : ℕ) : Prog → St → St → Prop
  | act {w wm im e} {s : St} : (s.act w wm im e).ih ≤ x.length + 1 → (s.act w wm im e).wh < B →
      Eval x B (.act w wm im e) s (s.act w wm im e)
  | skip {s : St} : Eval x B .skip s s
  | seq {p q} {s s1 s2 : St} : Eval x B p s s1 → Eval x B q s1 s2 → Eval x B (.seq p q) s s2
  | ite_t {c p q} {s s' : St} : s.test x c = true → Eval x B p s s' → Eval x B (.ite c p q) s s'
  | ite_f {c p q} {s s' : St} : s.test x c = false → Eval x B q s s' → Eval x B (.ite c p q) s s'
  | while_t {c p} {s s1 s2 : St} : s.test x c = true → Eval x B p s s1 →
      Eval x B (.while c p) s1 s2 → Eval x B (.while c p) s s2
  | while_f {c p} {s : St} : s.test x c = false → Eval x B (.while c p) s s

def rep (code : List Ins) (pc : ℕ) (s : St) : Configuration (toMachine code) :=
  ⟨if h : pc < code.length + 1 then some ⟨pc, h⟩ else none, s.ih, s.wh, 0, s.work, [], s.out⟩

/-- Reachability with the work bound enforced at every configuration after the first. -/
def Reach (M : Machine) (x : List Bool) (B : ℕ) : Configuration M → Configuration M → ℕ → Prop
  | c, c', 0 => c = c'
  | c, c', t + 1 => ∃ c1, M.step x c = some c1 ∧ c1.workHead < B ∧ Reach M x B c1 c' t

lemma Reach.trans {M : Machine} {x B} : ∀ {t1 : ℕ} {c1 c2 c3 : Configuration M} {t2 : ℕ},
    Reach M x B c1 c2 t1 → Reach M x B c2 c3 t2 → Reach M x B c1 c3 (t1 + t2)
  | 0, c1, c2, c3, t2, h1, h2 => by
    simp only [Reach] at h1; subst h1; simpa using h2
  | n + 1, c1, c2, c3, t2, h1, h2 => by
    obtain ⟨c, hc, hb, h⟩ := h1
    rw [show n + 1 + t2 = (n + t2) + 1 by omega]
    exact ⟨c, hc, hb, Reach.trans h h2⟩

lemma Reach.one {M : Machine} {x B} {c c1 : Configuration M} (h : M.step x c = some c1)
    (hb : c1.workHead < B) : Reach M x B c c1 1 := ⟨c1, h, hb, rfl⟩

def Embeds (code : List Ins) (a : ℕ) (l : List Ins) : Prop :=
  ∀ i < l.length, code[a + i]? = l[i]?

lemma Embeds.get {code a l} (h : Embeds code a l) {i : ℕ} (hi : i < l.length) :
    code[a + i]? = l[i]? := h i hi

lemma step_act (code : List Ins) (x : List Bool) (pc : ℕ) (hpc : pc < code.length)
    (w wm im e) (hc : code[pc]? = some (.act w wm im e)) (s : St)
    (hi : (s.act w wm im e).ih ≤ x.length + 1) :
    (toMachine code).step x (rep code pc s) = some (rep code (pc + 1) (s.act w wm im e)) := by
  have h1 : pc < code.length + 1 := by omega
  have h2 : pc + 1 < code.length + 1 := by omega
  have hi' : im.apply s.ih ≤ x.length + 1 := hi
  simp [Machine.step, rep, toMachine, h1, h2, hc, Ins.instr, St.act, hi']
  rfl


lemma step_br (code : List Ins) (x : List Bool) (pc : ℕ) (hpc : pc < code.length)
    (c t) (hc : code[pc]? = some (.br c t)) (ht : t ≤ code.length) (s : St)
    (hi : s.ih ≤ x.length + 1) :
    (toMachine code).step x (rep code pc s) =
      some (rep code (if s.test x c then t else pc + 1) s) := by
  have h1 : pc < code.length + 1 := by omega
  have h2 : pc + 1 < code.length + 1 := by omega
  have h3 : t < code.length + 1 := by omega
  by_cases hT : s.test x c = true
  · have hT' : c (if s.ih = 0 then none else x[s.ih - 1]?) (s.work s.wh) (s.ih == 0) (s.wh == 0)
        = true := hT
    simp [Machine.step, rep, toMachine, h1, h2, h3, hc, Ins.instr, hT, hT', Move.apply, hi]
  · have hF : s.test x c = false := by simpa using hT
    have hT' : c (if s.ih = 0 then none else x[s.ih - 1]?) (s.work s.wh) (s.ih == 0) (s.wh == 0)
        = false := hF
    simp [Machine.step, rep, toMachine, h1, h2, h3, hc, Ins.instr, hF, hT', Move.apply, hi]

lemma step_jmp (code : List Ins) (x : List Bool) (pc : ℕ) (hpc : pc < code.length)
    (t) (hc : code[pc]? = some (.jmp t)) (ht : t ≤ code.length) (s : St)
    (hi : s.ih ≤ x.length + 1) :
    (toMachine code).step x (rep code pc s) = some (rep code t s) := by
  have h1 : pc < code.length + 1 := by omega
  have h3 : t < code.length + 1 := by omega
  simp [Machine.step, rep, toMachine, h1, h3, hc, Ins.instr, Move.apply, hi]


lemma Embeds.append {code a l1 l2} (h : Embeds code a (l1 ++ l2)) :
    Embeds code a l1 ∧ Embeds code (a + l1.length) l2 := by
  constructor
  · intro i hi
    have := h i (by simp; omega)
    rwa [List.getElem?_append_left hi] at this
  · intro i hi
    have := h (l1.length + i) (by simp; omega)
    rw [List.getElem?_append_right (by omega)] at this
    simpa [← add_assoc] using this

lemma Eval.ih_le {x B p s s'} (h : Eval x B p s s') (hs : s.ih ≤ x.length + 1) :
    s'.ih ≤ x.length + 1 := by
  induction h with
  | act h1 _ => exact h1
  | skip => exact hs
  | seq _ _ ih1 ih2 => exact ih2 (ih1 hs)
  | ite_t _ _ ih => exact ih hs
  | ite_f _ _ ih => exact ih hs
  | while_t _ _ _ ih1 ih2 => exact ih2 (ih1 hs)
  | while_f _ => exact hs

lemma Eval.wh_lt {x B p s s'} (h : Eval x B p s s') (hs : s.wh < B) : s'.wh < B := by
  induction h with
  | act _ h2 => exact h2
  | skip => exact hs
  | seq _ _ ih1 ih2 => exact ih2 (ih1 hs)
  | ite_t _ _ ih => exact ih hs
  | ite_f _ _ ih => exact ih hs
  | while_t _ _ _ ih1 ih2 => exact ih2 (ih1 hs)
  | while_f _ => exact hs

theorem comp_correct (code : List Ins) (x : List Bool) (B : ℕ) (p : Prog) (s s' : St)
    (h : Eval x B p s s') : ∀ a, Embeds code a (p.comp a) → a + p.size ≤ code.length →
    s.ih ≤ x.length + 1 → s.wh < B →
    ∃ t, Reach (toMachine code) x B (rep code a s) (rep code (a + p.size) s') t := by
  induction h with
  | @act w wm im e s h1 h2 =>
    intro a hE hl hi hb
    refine ⟨1, Reach.one ?_ h2⟩
    · have := hE 0 (by simp [Prog.comp])
      have hc : code[a]? = some (.act w wm im e) := by simpa [Prog.comp] using this
      simpa [Prog.size] using step_act code x a (by simp [Prog.size] at hl; omega) w wm im e hc s h1
  | skip =>
    intro a hE hl hi hb
    exact ⟨0, rfl⟩
  | @seq p q s s1 s2 e1 e2 ih1 ih2 =>
    intro a hE hl hi hb
    simp only [Prog.comp] at hE
    obtain ⟨hE1, hE2⟩ := Embeds.append hE
    rw [Prog.comp_length] at hE2
    simp only [Prog.size] at hl
    obtain ⟨t1, r1⟩ := ih1 a hE1 (by omega) hi hb
    obtain ⟨t2, r2⟩ := ih2 (a + p.size) hE2 (by omega) (e1.ih_le hi) (e1.wh_lt hb)
    refine ⟨t1 + t2, ?_⟩
    rw [Prog.size, ← add_assoc]
    exact r1.trans r2
  | @ite_t c p q s s' ht e ih =>
    intro a hE hl hi hb
    simp only [Prog.comp] at hE
    simp only [List.append_assoc] at hE
    obtain ⟨hE0, hE'⟩ := Embeds.append hE
    obtain ⟨hEq, hE''⟩ := Embeds.append hE'
    obtain ⟨hEj, hEp⟩ := Embeds.append hE''
    simp only [List.length_append, List.length_singleton, Prog.comp_length] at hE0 hEq hEj hEp
    simp only [Prog.size] at hl ⊢
    have hbr : code[a]? = some (.br c (a + 1 + q.size + 1)) := by
      simpa using hE0 0 (by simp)
    have st := step_br code x a (by omega) c _ hbr (by omega) s hi
    rw [if_pos ht] at st
    have hEp' : Embeds code (a + q.size + 2) (p.comp (a + q.size + 2)) := by
      have := hEp
      rwa [show a + 1 + q.size + 1 = a + q.size + 2 by omega] at this
    obtain ⟨t, r⟩ := ih (a + q.size + 2) hEp' (by omega) hi hb
    refine ⟨1 + t, Reach.trans (Reach.one st hb) ?_⟩
    rw [show a + 1 + q.size + 1 = a + q.size + 2 by omega]
    rwa [show a + (q.size + p.size + 2) = a + q.size + 2 + p.size by omega]
  | @ite_f c p q s s' ht e ih =>
    intro a hE hl hi hb
    simp only [Prog.comp] at hE
    simp only [List.append_assoc] at hE
    obtain ⟨hE0, hE'⟩ := Embeds.append hE
    obtain ⟨hEq, hE''⟩ := Embeds.append hE'
    obtain ⟨hEj, hEp⟩ := Embeds.append hE''
    simp only [List.length_append, List.length_singleton, Prog.comp_length] at hE0 hEq hEj hEp
    simp only [Prog.size] at hl ⊢
    have hbr : code[a]? = some (.br c (a + 1 + q.size + 1)) := by
      simpa using hE0 0 (by simp)
    have st := step_br code x a (by omega) c _ hbr (by omega) s hi
    rw [if_neg (by simp [ht])] at st
    have hEq' : Embeds code (a + 1) (q.comp (a + 1)) := hEq
    obtain ⟨t, r⟩ := ih (a + 1) hEq' (by omega) hi hb
    have hjc : code[a + 1 + q.size]? = some (.jmp (a + q.size + p.size + 2)) := by
      simpa using hEj 0 (by simp)
    have st2 := step_jmp code x (a + 1 + q.size) (by omega) _ hjc (by omega) s'
      (e.ih_le hi)
    rw [show a + (q.size + p.size + 2) = a + q.size + p.size + 2 by omega]
    exact ⟨1 + (t + 1), Reach.trans (Reach.one st hb) (Reach.trans r
      (Reach.one st2 (e.wh_lt hb)))⟩
  | @while_t c p s s1 s2 ht e e2 ih1 ih2 =>
    intro a hE hl hi hb
    simp only [Prog.comp, List.append_assoc] at hE
    obtain ⟨hE0, hE'⟩ := Embeds.append hE
    obtain ⟨hEp, hEj⟩ := Embeds.append hE'
    simp only [List.length_append, List.length_singleton, Prog.comp_length] at hE0 hEp hEj
    simp only [Prog.size] at hl ⊢
    have hbr : code[a]? = some (.br (fun x w i o => !c x w i o) (a + p.size + 2)) := by
      simpa using hE0 0 (by simp)
    have st := step_br code x a (by omega) _ _ hbr (by omega) s hi
    rw [if_neg (by simp [St.test] at ht ⊢; simp [ht])] at st
    have hEp' : Embeds code (a + 1) (p.comp (a + 1)) := hEp
    obtain ⟨t, r⟩ := ih1 (a + 1) hEp' (by omega) hi hb
    have hjc : code[a + 1 + p.size]? = some (.jmp a) := by
      simpa using hEj 0 (by simp)
    have st2 := step_jmp code x (a + 1 + p.size) (by omega) _ hjc (by omega) s1 (e.ih_le hi)
    obtain ⟨t3, r3⟩ := ih2 a hE (by simpa [Prog.size] using hl) (e.ih_le hi) (e.wh_lt hb)
    refine ⟨1 + (t + (1 + t3)), Reach.trans (Reach.one st hb) (Reach.trans r
      (Reach.trans (Reach.one st2 (e.wh_lt hb)) r3))⟩
  | @while_f c p s ht =>
    intro a hE hl hi hb
    simp only [Prog.comp, List.append_assoc] at hE
    obtain ⟨hE0, hE'⟩ := Embeds.append hE
    simp only [Prog.size] at hl ⊢
    rw [← add_assoc]
    have hbr : code[a]? = some (.br (fun x w i o => !c x w i o) (a + p.size + 2)) := by
      simpa using hE0 0 (by simp)
    have st := step_br code x a (by omega) _ _ hbr (by omega) s hi
    rw [if_pos (by simp [St.test] at ht ⊢; simp [ht])] at st
    exact ⟨1, Reach.one st hb⟩


lemma run_of_reach (M : Machine) (x : List Bool) (B : ℕ) :
    ∀ (t : ℕ) (c c' : Configuration M), Reach M x B c c' t → c.workHead < B →
    ∀ t0, M.run x [] t0 = some c →
      M.run x [] (t0 + t) = some c' ∧ ∀ u ≤ t, ∀ d, M.run x [] (t0 + u) = some d → d.workHead < B
  | 0, c, c', h, hb, t0, hr => by
    simp only [Reach] at h; subst h
    refine ⟨hr, ?_⟩
    intro u hu d hd
    have : u = 0 := by omega
    subst this
    simp [hr] at hd; subst hd; exact hb
  | t + 1, c, c', h, hb, t0, hr => by
    obtain ⟨c1, hs, hb1, h1⟩ := h
    have hr1 : M.run x [] (t0 + 1) = some c1 := by
      simp [Machine.run, hr, hs]
    obtain ⟨r1, r2⟩ := run_of_reach M x B t c1 c' h1 hb1 (t0 + 1) hr1
    refine ⟨by rw [show t0 + (t + 1) = t0 + 1 + t by omega]; exact r1, ?_⟩
    intro u hu d hd
    rcases Nat.eq_zero_or_pos u with rfl | hu0
    · simp [hr] at hd; subst hd; exact hb
    · exact r2 (u - 1) (by omega) d (by rwa [show t0 + 1 + (u - 1) = t0 + u by omega])

theorem prints_of_eval (P : Prog) (x out : List Bool) (B : ℕ) (space : ℝ) (hB : B ≤ ⌈space⌉₊)
    (hB0 : 0 < B) (s' : St)
    (h : Eval x B P ⟨0, 0, fun _ => false, []⟩ s') (hout : s'.out = out) :
    CatalyticTreeEval.Main.Prints (toMachine (P.comp 0)) x out space := by
  have hi0 : (0 : ℕ) ≤ x.length + 1 := by omega
  obtain ⟨t, r⟩ := comp_correct (P.comp 0) x B P _ _ h 0 (fun i hi => by simp)
    (by simp [Prog.comp_length]) hi0 hB0
  have hinit : (toMachine (P.comp 0)).run x [] 0 = some (rep (P.comp 0) 0 ⟨0, 0, fun _ => false, []⟩) := by
    simp [Machine.run, Machine.initial, rep, toMachine]
  obtain ⟨r1, r2⟩ := run_of_reach _ x B t _ _ r hB0 0 hinit
  have hsz : (P.comp 0).length = P.size := Prog.comp_length P 0
  have hih := h.ih_le hi0
  have hwh := h.wh_lt hB0
  have hfin : (toMachine (P.comp 0)).step x (rep (P.comp 0) P.size s') =
      some ⟨none, s'.ih, s'.wh, 0, s'.work, [], s'.out⟩ := by
    have h1 : P.size < (P.comp 0).length + 1 := by omega
    have : (P.comp 0)[P.size]? = none := by
      rw [List.getElem?_eq_none]; omega
    simp [Machine.step, rep, toMachine, h1, this, Move.apply, hih]
  simp only [Nat.zero_add] at r1 r2
  refine ⟨t + 1, ⟨none, s'.ih, s'.wh, 0, s'.work, [], s'.out⟩, ?_, rfl, hout, ?_⟩
  · simp only [Machine.run, r1, Option.bind_some, hfin]
  · intro u hu d hd
    rcases Nat.lt_or_ge u (t + 1) with hlt | hge
    · exact lt_of_lt_of_le (r2 u (by omega) d hd) hB
    · have : u = t + 1 := by omega
      subst this
      simp only [Machine.run, r1, Option.bind_some, hfin, Option.some.injEq] at hd
      subst hd
      exact lt_of_lt_of_le hwh hB

def mvR : Prog := .act none .right .stay none
def mvL : Prog := .act none .left .stay none

def goR : ℕ → Prog
  | 0 => .skip
  | n + 1 => .seq mvR (goR n)

def home : Prog := .while (fun _ _ _ we => !we) mvL

lemma Eval.mvR' {x B ih wh T out} (hih : ih ≤ x.length + 1) (hb : wh + 1 < B) :
    Eval x B mvR ⟨ih, wh, T, out⟩ ⟨ih, wh + 1, T, out⟩ := by
  unfold mvR
  have := @Eval.act x B none .right .stay none ⟨ih, wh, T, out⟩ (by simpa [St.act, Move.apply] using hih)
    (by simpa [St.act, Move.apply] using hb)
  simpa [St.act, Move.apply] using this

lemma Eval.mvL' {x B ih wh T out} (hih : ih ≤ x.length + 1) (hb : wh < B) :
    Eval x B mvL ⟨ih, wh, T, out⟩ ⟨ih, wh - 1, T, out⟩ := by
  unfold mvL
  have := @Eval.act x B none .left .stay none ⟨ih, wh, T, out⟩ (by simpa [St.act, Move.apply] using hih)
    (by simp only [St.act, Move.apply]; omega)
  simpa [St.act, Move.apply] using this

lemma Eval.wrR {x B ih wh T out} (b : Bool) (m : Move) (hih : ih ≤ x.length + 1)
    (hb : m.apply wh < B) :
    Eval x B (.act (some b) m .stay none) ⟨ih, wh, T, out⟩
      ⟨ih, m.apply wh, Function.update T wh b, out⟩ := by
  have := @Eval.act x B (some b) m .stay none ⟨ih, wh, T, out⟩ (by simpa [St.act, Move.apply] using hih)
    (by simpa [St.act] using hb)
  simpa [St.act, Move.apply] using this

lemma Eval.goR' {x B ih T out} (hih : ih ≤ x.length + 1) :
    ∀ (n wh : ℕ), wh + n < B → Eval x B (goR n) ⟨ih, wh, T, out⟩ ⟨ih, wh + n, T, out⟩
  | 0, wh, _ => by simpa [goR] using (Eval.skip : Eval x B .skip ⟨ih, wh, T, out⟩ _)
  | n + 1, wh, hb => by
    have h1 := Eval.mvR' (x := x) (B := B) (T := T) (out := out) (wh := wh) hih (show wh + 1 < B by omega)
    have h2 := Eval.goR' (x := x) (B := B) (T := T) (out := out) hih n (wh + 1) (by omega)
    rw [show wh + (n + 1) = wh + 1 + n by omega]
    exact Eval.seq (p := mvR) (q := goR n) h1 h2

lemma Eval.home' {x B ih T out} (hih : ih ≤ x.length + 1) :
    ∀ (wh : ℕ), wh < B → Eval x B home ⟨ih, wh, T, out⟩ ⟨ih, 0, T, out⟩
  | 0, hb => by
    apply Eval.while_f
    simp [St.test]
  | wh + 1, hb => by
    apply Eval.while_t
    · simp [St.test]
    · exact Eval.mvL' hih hb
    · have := Eval.home' (x := x) (B := B) (T := T) (out := out) hih wh (by omega)
      unfold home at this
      simpa using this

lemma natLog_le_logb (n : ℕ) (hn : 0 < n) : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hn)]
  rw [Real.rpow_natCast]
  exact_mod_cast Nat.pow_log_le_self 2 hn.ne'



/-! ### Layer C: decoder program -/

lemma Eval.act' {x : List Bool} {B ih wh : ℕ} {T : ℕ → Bool} {out : List Bool}
    (w : Option Bool) (wm im : Move) (e : Option Bool)
    (h1 : im.apply ih ≤ x.length + 1) (h2 : wm.apply wh < B) :
    Eval x B (.act w wm im e) ⟨ih, wh, T, out⟩
      ⟨im.apply ih, wm.apply wh, Function.update T wh (w.getD (T wh)), out ++ e.toList⟩ :=
  Eval.act (s := ⟨ih, wh, T, out⟩) h1 h2

def Rl (w : ℕ) : ℕ → Bool := fun i => decide (i % 2 = 0 ∧ i < 2 * w)

def Tm (w lo n : ℕ) : ℕ → Bool := fun i =>
  decide (i % 2 = 0 ∧ i < 2 * w) || decide (i % 2 = 1 ∧ 2 * lo ≤ i ∧ i < 2 * n)

lemma Rl_zero : Rl 0 = fun _ => false := by
  funext i; simp [Rl]

lemma Tm_eq_Rl {w lo n : ℕ} (h : n ≤ lo) : Tm w lo n = Rl w := by
  funext i; simp only [Tm, Rl, Bool.or_eq_true, decide_eq_true_eq, Bool.decide_or]
  by_cases h1 : i % 2 = 0 ∧ i < 2 * w <;> simp [h1] <;> omega

lemma Rl_set (c : ℕ) : Function.update (Rl c) (2 * c) true = Rl (c + 1) := by
  funext i
  by_cases h : i = 2 * c
  · subst h; simp [Rl]
  · simp only [Function.update_apply, h, if_false, Rl]
    by_cases h1 : i % 2 = 0 ∧ i < 2 * c
    · simp [h1]; omega
    · simp [h1]; omega

lemma Rl_clr (c : ℕ) : Function.update (Rl (c + 1)) (2 * c) false = Rl c := by
  funext i
  by_cases h : i = 2 * c
  · subst h; simp [Rl]
  · simp only [Function.update_apply, h, if_false, Rl]
    by_cases h1 : i % 2 = 0 ∧ i < 2 * c
    · simp [h1]; omega
    · simp [h1]; omega

lemma Rl_clr' {b : ℕ} (hb : 1 ≤ b) : Function.update (Rl b) (2 * (b - 1)) false = Rl (b - 1) := by
  have := Rl_clr (b - 1)
  rwa [show b - 1 + 1 = b by omega] at this

lemma Tm_mark (w c : ℕ) : Function.update (Tm w 0 c) (2 * c + 1) true = Tm w 0 (c + 1) := by
  funext i
  by_cases h : i = 2 * c + 1
  · subst h; simp [Tm]; omega
  · simp only [Function.update_apply, h, if_false, Tm]
    rw [Bool.eq_iff_iff]; simp; omega

lemma Tm_unmark (w lo n : ℕ) (h : lo < n) :
    Function.update (Tm w lo n) (2 * lo + 1) false = Tm w (lo + 1) n := by
  funext i
  by_cases hi : i = 2 * lo + 1
  · subst hi; simp [Tm]; omega
  · simp only [Function.update_apply, hi, if_false, Tm]
    rw [Bool.eq_iff_iff]; simp; omega

/-! unary loop writing the ruler -/

def uBody : Prog := .seq (.act (some true) .right .right none) mvR
def uLoop : Prog := .while (fun a _ _ _ => a == some true) uBody

lemma uLoop_spec {x : List Bool} {B : ℕ} (n : ℕ) : ∀ (c ih : ℕ) (out : List Bool),
    1 ≤ ih → (∀ i < n, x[ih - 1 + i]? = some true) → x[ih - 1 + n]? = some false →
    2 * (c + n) < B →
    Eval x B uLoop ⟨ih, 2 * c, Rl c, out⟩ ⟨ih + n, 2 * (c + n), Rl (c + n), out⟩ := by
  induction n with
  | zero =>
    intro c ih out h1 hs hm hb
    apply Eval.while_f
    simp only [Nat.add_zero] at hm
    simp [St.test, show ih ≠ 0 by omega, hm]
  | succ n ih_ =>
    intro c ih out h1 hs hm hb
    have hlen : ih - 1 + (n + 1) < x.length := by
      by_contra hh
      rw [List.getElem?_eq_none (by omega)] at hm; simp at hm
    have h0 := hs 0 (by omega)
    simp only [Nat.add_zero] at h0
    apply Eval.while_t (s1 := ⟨ih + 1, 2 * (c + 1), Rl (c + 1), out⟩)
    · simp [St.test, show ih ≠ 0 by omega, h0]
    · unfold uBody
      have e1 := Eval.act' (x := x) (B := B) (T := Rl c) (out := out) (ih := ih) (wh := 2 * c)
        (some true) .right .right none (by simp [Move.apply]; omega) (by simp [Move.apply]; omega)
      have e2 := Eval.mvR' (x := x) (B := B) (ih := ih + 1) (wh := 2 * c + 1)
        (T := Function.update (Rl c) (2 * c) true) (out := out) (by omega) (by omega)
      simp only [Move.apply, Option.getD_some, Option.toList_none, List.append_nil, Rl_set] at e1 e2
      rw [show 2 * (c + 1) = 2 * c + 1 + 1 by omega]
      exact Eval.seq e1 e2
    · have := ih_ (c + 1) (ih + 1) out (by omega)
        (fun i hi => by
          have := hs (i + 1) (by omega)
          rwa [show ih - 1 + (i + 1) = ih + 1 - 1 + i by omega] at this)
        (by rwa [show ih + 1 - 1 + n = ih - 1 + (n + 1) by omega]) (by omega)
      rw [show c + 1 + n = c + (n + 1) by omega, show ih + 1 + n = ih + (n + 1) by omega] at this
      exact this

/-! going back along the ruler, consuming bits -/

def backBody : Prog := .seq mvL (.seq mvL (.act none .stay .right none))
def backKeep : Prog := .while (fun _ _ _ we => !we) backBody
def backBodyC : Prog := .seq mvL (.seq mvL (.act (some false) .stay .right none))
def backClr : Prog := .while (fun _ _ _ we => !we) backBodyC

lemma backKeep_spec {x : List Bool} {B : ℕ} (T : ℕ → Bool) : ∀ (c ih : ℕ) (out : List Bool),
    ih + c ≤ x.length + 1 → 2 * c < B →
    Eval x B backKeep ⟨ih, 2 * c, T, out⟩ ⟨ih + c, 0, T, out⟩ := by
  intro c
  induction c with
  | zero =>
    intro ih out h1 hb
    apply Eval.while_f
    simp [St.test]
  | succ c ih_ =>
    intro ih out h1 hb
    apply Eval.while_t (s1 := ⟨ih + 1, 2 * c, T, out⟩)
    · simp [St.test]
    · unfold backBody
      have e1 := Eval.mvL' (x := x) (B := B) (ih := ih) (wh := 2 * (c + 1)) (T := T) (out := out) (by omega) (by omega)
      have e2 := Eval.mvL' (x := x) (B := B) (ih := ih) (wh := 2 * (c + 1) - 1) (T := T) (out := out) (by omega) (by omega)
      have e3 := Eval.act' (x := x) (B := B) (T := T) (out := out) (ih := ih) (wh := 2 * (c + 1) - 1 - 1)
        none .stay .right none (by simp [Move.apply]; omega) (by simp [Move.apply]; omega)
      simp only [Move.apply, Option.getD_none, Function.update_eq_self, Option.toList_none, List.append_nil] at e3
      rw [show 2 * (c + 1) - 1 - 1 = 2 * c by omega] at e2 e3
      exact Eval.seq e1 (Eval.seq e2 e3)
    · have := ih_ (ih + 1) out (by omega) (by omega)
      rw [show ih + 1 + c = ih + (c + 1) by omega] at this
      exact this

lemma backClr_spec {x : List Bool} {B : ℕ} : ∀ (c ih : ℕ) (out : List Bool),
    ih + c ≤ x.length + 1 → 2 * c < B →
    Eval x B backClr ⟨ih, 2 * c, Rl c, out⟩ ⟨ih + c, 0, fun _ => false, out⟩ := by
  intro c
  induction c with
  | zero =>
    intro ih out h1 hb
    rw [← Rl_zero]
    apply Eval.while_f
    simp [St.test]
  | succ c ih_ =>
    intro ih out h1 hb
    apply Eval.while_t (s1 := ⟨ih + 1, 2 * c, Rl c, out⟩)
    · simp [St.test]
    · unfold backBodyC
      have e1 := Eval.mvL' (x := x) (B := B) (ih := ih) (wh := 2 * (c + 1)) (T := Rl (c + 1)) (out := out) (by omega) (by omega)
      have e2 := Eval.mvL' (x := x) (B := B) (ih := ih) (wh := 2 * (c + 1) - 1) (T := Rl (c + 1)) (out := out) (by omega) (by omega)
      have e3 := Eval.act' (x := x) (B := B) (T := Rl (c + 1)) (out := out) (ih := ih) (wh := 2 * (c + 1) - 1 - 1)
        (some false) .stay .right none (by simp [Move.apply]; omega) (by simp [Move.apply]; omega)
      rw [show 2 * (c + 1) - 1 - 1 = 2 * c by omega] at e2 e3
      simp only [Move.apply, Option.getD_some, Option.toList_none, List.append_nil, Rl_clr] at e3
      exact Eval.seq e1 (Eval.seq e2 e3)
    · have := ih_ (ih + 1) out (by omega) (by omega)
      rw [show ih + 1 + c = ih + (c + 1) by omega] at this
      exact this

/-! ### skip and read of a code word -/

def mvI : Prog := .act none .stay .right none
def mvIL : Prog := .act none .stay .left none

lemma Eval.mvI' {x : List Bool} {B ih wh : ℕ} {T : ℕ → Bool} {out : List Bool}
    (h1 : ih + 1 ≤ x.length + 1) (hb : wh < B) :
    Eval x B mvI ⟨ih, wh, T, out⟩ ⟨ih + 1, wh, T, out⟩ := by
  have := Eval.act' (x := x) (B := B) (T := T) (out := out) (ih := ih) (wh := wh)
    none .stay .right none (by simpa [Move.apply] using h1) (by simpa [Move.apply] using hb)
  unfold mvI
  simpa [Move.apply] using this

lemma Eval.mvIL' {x : List Bool} {B ih wh : ℕ} {T : ℕ → Bool} {out : List Bool}
    (h1 : ih ≤ x.length + 1) (hb : wh < B) :
    Eval x B mvIL ⟨ih, wh, T, out⟩ ⟨ih - 1, wh, T, out⟩ := by
  have := Eval.act' (x := x) (B := B) (T := T) (out := out) (ih := ih) (wh := wh)
    none .stay .left none (by simp [Move.apply]; omega) (by simpa [Move.apply] using hb)
  unfold mvIL
  simpa [Move.apply] using this

def skipP : Prog := .seq uLoop (.seq mvI backClr)

lemma skipP_spec {x : List Bool} {B : ℕ} (b ih : ℕ) (out : List Bool)
    (h1 : 1 ≤ ih) (hs : ∀ i < b, x[ih - 1 + i]? = some true) (hm : x[ih - 1 + b]? = some false)
    (hl : ih + 2 * b + 1 ≤ x.length + 1) (hb : 2 * b < B) :
    Eval x B skipP ⟨ih, 0, fun _ => false, out⟩ ⟨ih + 2 * b + 1, 0, fun _ => false, out⟩ := by
  have e1 := uLoop_spec (x := x) (B := B) b 0 ih out h1 hs hm (by omega)
  rw [Rl_zero] at e1
  have e2 := Eval.mvI' (x := x) (B := B) (ih := ih + b) (wh := 2 * (0 + b)) (T := Rl (0 + b)) (out := out)
    (by omega) (by omega)
  have e3 := backClr_spec (x := x) (B := B) (0 + b) (ih + b + 1) out (by omega) (by omega)
  have := Eval.seq e1 (Eval.seq e2 e3)
  rw [show ih + b + 1 + (0 + b) = ih + 2 * b + 1 by omega] at this
  unfold skipP
  simpa using this

def scanP : Prog := .while (fun _ w _ _ => w) (.seq mvR mvR)

lemma scanP_spec {x : List Bool} {B : ℕ} (b ih : ℕ) (out : List Bool) (hih : ih ≤ x.length + 1)
    (hb : 2 * b < B) : ∀ r c, c + r = b →
    Eval x B scanP ⟨ih, 2 * c, Rl b, out⟩ ⟨ih, 2 * b, Rl b, out⟩ := by
  intro r
  induction r with
  | zero =>
    intro c hc
    obtain rfl : c = b := by omega
    apply Eval.while_f
    simp [St.test, Rl]
  | succ r ih_ =>
    intro c hc
    apply Eval.while_t (s1 := ⟨ih, 2 * (c + 1), Rl b, out⟩)
    · simp [St.test, Rl]; omega
    · have e1 := Eval.mvR' (x := x) (B := B) (ih := ih) (wh := 2 * c) (T := Rl b) (out := out) hih (by omega)
      have e2 := Eval.mvR' (x := x) (B := B) (ih := ih) (wh := 2 * c + 1) (T := Rl b) (out := out) hih (by omega)
      rw [show 2 * (c + 1) = 2 * c + 1 + 1 by omega]
      exact Eval.seq e1 e2
    · exact ih_ (c + 1) (by omega)

def eraseP : Prog := .seq scanP (.seq mvL (.seq mvL (.seq (.act (some false) .stay .stay none) home)))

def fixP : Prog :=
  .seq mvIL (.seq (.ite (fun a _ _ _ => a == some false) eraseP .skip) mvI)

lemma fixP_spec {x : List Bool} {B : ℕ} (b ih' : ℕ) (out : List Bool) (hb1 : 1 ≤ b) (h2 : 2 ≤ ih')
    (hih : ih' ≤ x.length + 1) (hb : 2 * b < B) :
    Eval x B fixP ⟨ih', 0, Rl b, out⟩
      ⟨ih', 0, Rl (if x[ih' - 2]? = some false then b - 1 else b), out⟩ := by
  have e1 := Eval.mvIL' (x := x) (B := B) (wh := 0) (T := Rl b) (out := out) hih (by omega)
  have e3 := Eval.mvI' (x := x) (B := B) (ih := ih' - 1) (wh := 0) (T := Rl (if x[ih' - 2]? = some false then b - 1 else b)) (out := out) (by omega) (by omega)
  rw [show ih' - 1 + 1 = ih' by omega] at e3
  by_cases hl : x[ih' - 2]? = some false
  · simp only [hl, if_true] at e3 ⊢
    have s1 := scanP_spec (x := x) (B := B) b (ih' - 1) out (by omega) hb b 0 (by omega)
    have s2 := Eval.mvL' (x := x) (B := B) (ih := ih' - 1) (wh := 2 * b) (T := Rl b) (out := out) (by omega) (by omega)
    have s3 := Eval.mvL' (x := x) (B := B) (ih := ih' - 1) (wh := 2 * b - 1) (T := Rl b) (out := out) (by omega) (by omega)
    have s4 := Eval.act' (x := x) (B := B) (T := Rl b) (out := out) (ih := ih' - 1) (wh := 2 * b - 1 - 1)
      (some false) .stay .stay none (by simp [Move.apply]; omega) (by simp [Move.apply]; omega)
    rw [show 2 * b - 1 - 1 = 2 * (b - 1) by omega] at s3 s4
    simp only [Move.apply, Option.getD_some, Option.toList_none, List.append_nil, Rl_clr' hb1] at s4
    have s5 := Eval.home' (x := x) (B := B) (ih := ih' - 1) (T := Rl (b - 1)) (out := out) (by omega) (2 * (b - 1)) (by omega)
    have mid : Eval x B (.ite (fun a _ _ _ => a == some false) eraseP .skip) ⟨ih' - 1, 0, Rl b, out⟩
        ⟨ih' - 1, 0, Rl (b - 1), out⟩ := by
      apply Eval.ite_t
      · simp [St.test, show ih' - 1 ≠ 0 by omega, hl]
        have : ih' - 1 - 1 = ih' - 2 := by omega
        rw [this]; exact hl
      · unfold eraseP
        exact Eval.seq s1 (Eval.seq s2 (Eval.seq s3 (Eval.seq s4 s5)))
    exact Eval.seq e1 (Eval.seq mid e3)
  · simp only [hl, if_false] at e3 ⊢
    have mid : Eval x B (.ite (fun a _ _ _ => a == some false) eraseP .skip) ⟨ih' - 1, 0, Rl b, out⟩
        ⟨ih' - 1, 0, Rl b, out⟩ := by
      apply Eval.ite_f
      · simp [St.test, show ih' - 1 ≠ 0 by omega]
        have : ih' - 1 - 1 = ih' - 2 := by omega
        rw [this]; exact hl
      · exact Eval.skip
    exact Eval.seq e1 (Eval.seq mid e3)

def readP : Prog := .seq uLoop (.seq mvI (.seq backKeep fixP))

lemma readP_spec {x : List Bool} {B : ℕ} (b ih : ℕ) (out : List Bool)
    (hb1 : 1 ≤ b) (h1 : 1 ≤ ih) (hs : ∀ i < b, x[ih - 1 + i]? = some true) (hm : x[ih - 1 + b]? = some false)
    (hl : ih + 2 * b + 1 ≤ x.length + 1) (hb : 2 * b < B) :
    Eval x B readP ⟨ih, 0, fun _ => false, out⟩
      ⟨ih + 2 * b + 1, 0, Rl (if x[ih + 2 * b - 1]? = some false then b - 1 else b), out⟩ := by
  have e1 := uLoop_spec (x := x) (B := B) b 0 ih out h1 hs hm (by omega)
  rw [Rl_zero] at e1
  have e2 := Eval.mvI' (x := x) (B := B) (ih := ih + b) (wh := 2 * (0 + b)) (T := Rl (0 + b)) (out := out)
    (by omega) (by omega)
  have e3 := backKeep_spec (x := x) (B := B) (Rl (0 + b)) (0 + b) (ih + b + 1) out (by omega) (by omega)
  simp only [Nat.zero_add] at e1 e2 e3
  have e4 := fixP_spec (x := x) (B := B) b (ih + b + 1 + b) out hb1 (by omega) (by omega) hb
  have := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))
  rw [show ih + b + 1 + b = ih + 2 * b + 1 by omega] at this
  simp only [show ih + 2 * b + 1 - 2 = ih + 2 * b - 1 by omega] at this
  exact this

def goI : ℕ → Prog
  | 0 => .skip
  | n + 1 => .seq mvI (goI n)

lemma goI_spec {x : List Bool} {B : ℕ} {wh : ℕ} {T : ℕ → Bool} {out : List Bool} (hw : wh < B) :
    ∀ n ih, ih + n ≤ x.length + 1 → Eval x B (goI n) ⟨ih, wh, T, out⟩ ⟨ih + n, wh, T, out⟩
  | 0, ih, _ => Eval.skip
  | n + 1, ih, h => by
    have e1 := Eval.mvI' (x := x) (B := B) (ih := ih) (wh := wh) (T := T) (out := out) (by omega) hw
    have e2 := goI_spec (x := x) (B := B) (T := T) (out := out) hw n (ih + 1) (by omega)
    rw [show ih + (n + 1) = ih + 1 + n by omega]
    exact (Eval.seq e1 e2 : Eval x B (Prog.seq mvI (goI n)) _ _)

/-! ### pattern test for the code of 0 -/

def pat (k : Bool → Prog) : Prog :=
  .ite (fun a _ _ _ => a == some true)
    (.seq mvI (.ite (fun a _ _ _ => a == some false)
      (.seq mvI (.ite (fun a _ _ _ => a == some false)
        (.seq mvIL (.seq mvIL (k true))) (.seq mvIL (.seq mvIL (k false)))))
      (.seq mvIL (k false))))
    (k false)

lemma pat_spec (k : Bool → Prog) {x : List Bool} {B ih wh : ℕ} {T : ℕ → Bool} {out : List Bool}
    {s' : St} (h1 : 1 ≤ ih) (h2 : ih + 2 ≤ x.length + 1) (hw : wh < B)
    (H : Eval x B (k (decide (x[ih - 1]? = some true ∧ x[ih]? = some false ∧ x[ih + 1]? = some false)))
      ⟨ih, wh, T, out⟩ s') :
    Eval x B (pat k) ⟨ih, wh, T, out⟩ s' := by
  have m1 := Eval.mvI' (x := x) (B := B) (ih := ih) (wh := wh) (T := T) (out := out) (by omega) hw
  have m2 := Eval.mvI' (x := x) (B := B) (ih := ih + 1) (wh := wh) (T := T) (out := out) (by omega) hw
  have b1 := Eval.mvIL' (x := x) (B := B) (ih := ih + 1 + 1) (wh := wh) (T := T) (out := out) (by omega) hw
  have b2 := Eval.mvIL' (x := x) (B := B) (ih := ih + 1 + 1 - 1) (wh := wh) (T := T) (out := out) (by omega) hw
  have b3 := Eval.mvIL' (x := x) (B := B) (ih := ih + 1) (wh := wh) (T := T) (out := out) (by omega) hw
  simp only [Nat.add_sub_cancel] at b2 b3
  unfold pat
  by_cases a1 : x[ih - 1]? = some true
  · apply Eval.ite_t (by simp [St.test, show ih ≠ 0 by omega, a1])
    refine Eval.seq m1 ?_
    by_cases a2 : x[ih]? = some false
    · apply Eval.ite_t (by simp [St.test, a2])
      refine Eval.seq m2 ?_
      by_cases a3 : x[ih + 1]? = some false
      · apply Eval.ite_t (by simp [St.test, a3])
        have hd : decide (x[ih - 1]? = some true ∧ x[ih]? = some false ∧ x[ih + 1]? = some false) = true := by
          simp [a1, a2, a3]
        rw [hd] at H
        exact Eval.seq b1 (Eval.seq b2 H)
      · apply Eval.ite_f (by simp [St.test, a3])
        have hd : decide (x[ih - 1]? = some true ∧ x[ih]? = some false ∧ x[ih + 1]? = some false) = false := by
          simp [a3]
        rw [hd] at H
        exact Eval.seq b1 (Eval.seq b2 H)
    · apply Eval.ite_f (by simp [St.test, a2])
      have hd : decide (x[ih - 1]? = some true ∧ x[ih]? = some false ∧ x[ih + 1]? = some false) = false := by
        simp [a2]
      rw [hd] at H
      exact Eval.seq b3 H
  · apply Eval.ite_f (by simp [St.test, show ih ≠ 0 by omega, a1])
    have hd : decide (x[ih - 1]? = some true ∧ x[ih]? = some false ∧ x[ih + 1]? = some false) = false := by
      simp [a1]
    rw [hd] at H
    exact H

/-! ### emitting the padded shift and the term -/

def markBody : Prog := .seq mvR (.act (some true) .right .right none)
def markLoop : Prog := .while (fun a _ _ _ => a == some true) markBody

lemma markLoop_spec {x : List Bool} {B : ℕ} (w n : ℕ) : ∀ (c ih : ℕ) (out : List Bool),
    1 ≤ ih → (∀ i < n, x[ih - 1 + i]? = some true) → x[ih - 1 + n]? = some false →
    2 * (c + n) < B →
    Eval x B markLoop ⟨ih, 2 * c, Tm w 0 c, out⟩ ⟨ih + n, 2 * (c + n), Tm w 0 (c + n), out⟩ := by
  induction n with
  | zero =>
    intro c ih out h1 hs hm hb
    apply Eval.while_f
    simp only [Nat.add_zero] at hm
    simp [St.test, show ih ≠ 0 by omega, hm]
  | succ n ih_ =>
    intro c ih out h1 hs hm hb
    have hlen : ih - 1 + (n + 1) < x.length := by
      by_contra hh
      rw [List.getElem?_eq_none (by omega)] at hm; simp at hm
    have h0 := hs 0 (by omega)
    simp only [Nat.add_zero] at h0
    apply Eval.while_t (s1 := ⟨ih + 1, 2 * (c + 1), Tm w 0 (c + 1), out⟩)
    · simp [St.test, show ih ≠ 0 by omega, h0]
    · unfold markBody
      have e1 := Eval.mvR' (x := x) (B := B) (ih := ih) (wh := 2 * c) (T := Tm w 0 c) (out := out)
        (by omega) (by omega)
      have e2 := Eval.act' (x := x) (B := B) (T := Tm w 0 c) (out := out) (ih := ih) (wh := 2 * c + 1)
        (some true) .right .right none (by simp [Move.apply]; omega) (by simp [Move.apply]; omega)
      simp only [Move.apply, Option.getD_some, Option.toList_none, List.append_nil, Tm_mark] at e2
      rw [show 2 * (c + 1) = 2 * c + 1 + 1 by omega]
      exact Eval.seq e1 e2
    · have := ih_ (c + 1) (ih + 1) out (by omega)
        (fun i hi => by
          have := hs (i + 1) (by omega)
          rwa [show ih - 1 + (i + 1) = ih + 1 - 1 + i by omega] at this)
        (by rwa [show ih + 1 - 1 + n = ih - 1 + (n + 1) by omega]) (by omega)
      rw [show c + 1 + n = c + (n + 1) by omega, show ih + 1 + n = ih + (n + 1) by omega] at this
      exact this

def emitBody : Prog :=
  .seq mvR (.ite (fun _ w _ _ => w)
    (.ite (fun a _ _ _ => a == some true)
      (.act (some false) .right .right (some true)) (.act (some false) .right .right (some false)))
    (.act none .right .stay (some false)))
def emitLoop : Prog := .while (fun _ w _ _ => w) emitBody

lemma mapRange_succ {α : Type} (g : ℕ → α) (c r : ℕ) :
    (List.range (r + 1)).map (fun i => g (c + i)) = g c :: (List.range r).map (fun i => g (c + 1 + i)) := by
  rw [List.range_succ_eq_map]
  simp [Function.comp, Nat.add_assoc, Nat.add_comm 1]

lemma Tm_odd (w c n : ℕ) : Tm w c n (2 * c + 1) = decide (c < n) := by
  rw [Bool.eq_iff_iff]; simp [Tm]; omega

lemma Tm_even (w c n : ℕ) (h : c < w) : Tm w c n (2 * c) = true := by
  simp [Tm]; omega

lemma emit_spec {x : List Bool} {B : ℕ} (f : ℕ → Bool) (w n ih0 : ℕ) (hn : n ≤ w) (hih0 : 1 ≤ ih0)
    (hx : ∀ i < n, x[ih0 - 1 + i]? = some (f i)) (hlen : ih0 + n ≤ x.length + 1) (hb : 2 * w < B) :
    ∀ r c (out : List Bool), c + r = w →
    Eval x B emitLoop ⟨ih0 + min c n, 2 * c, Tm w c n, out⟩
      ⟨ih0 + n, 2 * w, Rl w, out ++ (List.range r).map (fun i => if c + i < n then f (c + i) else false)⟩ := by
  intro r
  induction r with
  | zero =>
    intro c out hc
    obtain rfl : c = w := by omega
    rw [Tm_eq_Rl hn, min_eq_right hn]
    simp only [List.range_zero, List.map_nil, List.append_nil]
    apply Eval.while_f
    simp [St.test, Rl]
  | succ r ih_ =>
    intro c out hc
    have hcw : c < w := by omega
    have te := Tm_even w c n hcw
    have tm := Tm_odd w c n
    have hih : ih0 + min c n ≤ x.length + 1 := by omega
    by_cases hcn : c < n
    · have hfc := hx c hcn
      have hmin : min c n = c := min_eq_left hcn.le
      have hmin' : min (c + 1) n = c + 1 := min_eq_left hcn
      rw [hmin]
      have hsym : x[ih0 + c - 1]? = some (f c) := by
        rwa [show ih0 + c - 1 = ih0 - 1 + c by omega]
      have step : Eval x B emitBody ⟨ih0 + c, 2 * c, Tm w c n, out⟩
          ⟨ih0 + c + 1, 2 * c + 1 + 1, Tm w (c + 1) n, out ++ [f c]⟩ := by
        have e1 := Eval.mvR' (x := x) (B := B) (ih := ih0 + c) (wh := 2 * c) (T := Tm w c n) (out := out)
          (by omega) (by omega)
        refine Eval.seq e1 ?_
        have key : Eval x B (.ite (fun a _ _ _ => a == some true)
            (.act (some false) .right .right (some true)) (.act (some false) .right .right (some false)))
            ⟨ih0 + c, 2 * c + 1, Tm w c n, out⟩
            ⟨ih0 + c + 1, 2 * c + 1 + 1, Tm w (c + 1) n, out ++ [f c]⟩ := by
          have a1 := Eval.act' (x := x) (B := B) (T := Tm w c n) (out := out) (ih := ih0 + c) (wh := 2 * c + 1)
            (some false) .right .right (some (f c)) (by simp [Move.apply]; omega) (by simp [Move.apply]; omega)
          simp only [Move.apply, Option.getD_some, Option.toList_some, Tm_unmark w c n hcn] at a1
          have a2 := Eval.act' (x := x) (B := B) (T := Tm w c n) (out := out) (ih := ih0 + c) (wh := 2 * c + 1)
            (some false) .right .right (some true) (by simp [Move.apply]; omega) (by simp [Move.apply]; omega)
          simp only [Move.apply, Option.getD_some, Option.toList_some, Tm_unmark w c n hcn] at a2
          have a3 := Eval.act' (x := x) (B := B) (T := Tm w c n) (out := out) (ih := ih0 + c) (wh := 2 * c + 1)
            (some false) .right .right (some false) (by simp [Move.apply]; omega) (by simp [Move.apply]; omega)
          simp only [Move.apply, Option.getD_some, Option.toList_some, Tm_unmark w c n hcn] at a3
          cases hf : f c
          · apply Eval.ite_f
            · simp [St.test, show ih0 ≠ 0 by omega, hsym, hf]
            · rw [hf] at a1; simpa [hf] using a3
          · apply Eval.ite_t
            · simp [St.test, show ih0 ≠ 0 by omega, hsym, hf]
            · simpa [hf] using a2
        apply Eval.ite_t _ key
        simp [St.test, tm, hcn]
      have rc := ih_ (c + 1) (out ++ [f c]) (by omega)
      rw [hmin', ← Nat.add_assoc] at rc
      refine Eval.while_t (by simp [St.test, te]) step ?_
      rw [show 2 * (c + 1) = 2 * c + 1 + 1 by omega] at rc
      have e := mapRange_succ (fun i => if i < n then f i else false) c r
      simp only [hcn, if_true] at e ⊢
      rw [e]
      simp only [List.append_assoc, List.singleton_append] at rc ⊢
      exact rc
    · have hmin : min c n = n := min_eq_right (by omega)
      have hmin' : min (c + 1) n = n := min_eq_right (by omega)
      rw [hmin]
      have step : Eval x B emitBody ⟨ih0 + n, 2 * c, Tm w c n, out⟩
          ⟨ih0 + n, 2 * c + 1 + 1, Tm w c n, out ++ [false]⟩ := by
        have e1 := Eval.mvR' (x := x) (B := B) (ih := ih0 + n) (wh := 2 * c) (T := Tm w c n) (out := out)
          (by omega) (by omega)
        refine Eval.seq e1 ?_
        apply Eval.ite_f
        · simp [St.test, tm, hcn]
        · have a := Eval.act' (x := x) (B := B) (T := Tm w c n) (out := out) (ih := ih0 + n) (wh := 2 * c + 1)
            none .right .stay (some false) (by simp [Move.apply]; omega) (by simp [Move.apply]; omega)
          simpa [Move.apply] using a
      have rc := ih_ (c + 1) (out ++ [false]) (by omega)
      have t1 : Tm w (c + 1) n = Tm w c n := by
        rw [Tm_eq_Rl (by omega), Tm_eq_Rl (by omega)]
      rw [hmin', t1] at rc
      refine Eval.while_t (by simp [St.test, te]) step ?_
      rw [show 2 * (c + 1) = 2 * c + 1 + 1 by omega] at rc
      have e := mapRange_succ (fun i => if i < n then f i else false) c r
      simp only [hcn, if_false] at e ⊢
      rw [e]
      simp only [List.append_assoc, List.singleton_append] at rc ⊢
      exact rc

def jP : Prog := .seq markLoop (.seq mvI (.seq home (.seq emitLoop home)))

lemma jP_spec {x : List Bool} {B : ℕ} (f : ℕ → Bool) (w n ih : ℕ) (out : List Bool)
    (hn : n ≤ w) (h1 : 1 ≤ ih)
    (hs : ∀ i < n, x[ih - 1 + i]? = some true) (hm : x[ih - 1 + n]? = some false)
    (hx : ∀ i < n, x[ih + n + i]? = some (f i)) (hlen : ih + 2 * n + 1 ≤ x.length + 1)
    (hb : 2 * w < B) :
    Eval x B jP ⟨ih, 0, Rl w, out⟩
      ⟨ih + 2 * n + 1, 0, Rl w, out ++ (List.range w).map (fun i => if i < n then f i else false)⟩ := by
  have hT : Rl w = Tm w 0 0 := (Tm_eq_Rl (le_refl 0)).symm
  have e1 := markLoop_spec (x := x) (B := B) w n 0 ih out h1 hs hm (by omega)
  rw [← hT] at e1
  have e2 := Eval.mvI' (x := x) (B := B) (ih := ih + n) (wh := 2 * (0 + n)) (T := Tm w 0 (0 + n)) (out := out)
    (by omega) (by omega)
  have e3 := Eval.home' (x := x) (B := B) (ih := ih + n + 1) (T := Tm w 0 (0 + n)) (out := out)
    (by omega) (2 * (0 + n)) (by omega)
  have e4 := emit_spec (x := x) (B := B) f w n (ih + n + 1) hn (by omega)
    (fun i hi => by rw [show ih + n + 1 - 1 + i = ih + n + i by omega]; exact hx i hi) (by omega) hb
    w 0 out (by omega)
  simp only [Nat.zero_add, Nat.zero_le, min_eq_left, Nat.mul_zero, Nat.add_zero] at e1 e2 e3 e4
  have e5 := Eval.home' (x := x) (B := B) (ih := ih + n + 1 + n) (T := Rl w) (out := out ++ (List.range w).map (fun i => if i < n then f i else false)) (by omega) (2 * w) hb
  unfold jP
  have := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))
  rw [show ih + n + 1 + n = ih + 2 * n + 1 by omega] at this
  exact this

def tailLoop : Prog := .while (fun _ w _ _ => w) (.seq (.act none .right .stay (some false)) mvR)

lemma tailLoop_spec {x : List Bool} {B : ℕ} (w ih : ℕ) (hih : ih ≤ x.length + 1)
    (hb : 2 * w < B) : ∀ r c (out : List Bool), c + r = w →
    Eval x B tailLoop ⟨ih, 2 * c, Rl w, out⟩ ⟨ih, 2 * w, Rl w, out ++ List.replicate r false⟩ := by
  intro r
  induction r with
  | zero =>
    intro c out hc
    obtain rfl : c = w := by omega
    simp only [List.replicate_zero, List.append_nil]
    apply Eval.while_f
    simp [St.test, Rl]
  | succ r ih_ =>
    intro c out hc
    apply Eval.while_t (s1 := ⟨ih, 2 * (c + 1), Rl w, out ++ [false]⟩)
    · simp [St.test, Rl]; omega
    · have e1 := Eval.act' (x := x) (B := B) (T := Rl w) (out := out) (ih := ih) (wh := 2 * c)
        none .right .stay (some false) (by simpa [Move.apply] using hih) (by simp [Move.apply]; omega)
      simp only [Move.apply, Option.getD_none, Function.update_eq_self, Option.toList_some] at e1
      have e2 := Eval.mvR' (x := x) (B := B) (ih := ih) (wh := 2 * c + 1) (T := Rl w) (out := out ++ [false]) hih (by omega)
      rw [show 2 * (c + 1) = 2 * c + 1 + 1 by omega]
      exact Eval.seq e1 e2
    · have := ih_ (c + 1) (out ++ [false]) (by omega)
      rw [List.append_assoc] at this
      simp only [List.replicate_succ, List.singleton_append] at this ⊢
      exact this

def termP (e0 e1 : Bool) : Prog :=
  .seq (.act none .stay .stay (some e0)) (.seq (goR 2) (.seq (.act none .stay .stay (some e1))
    (.seq (goR 2) (.seq tailLoop home))))

lemma termP_spec {x : List Bool} {B : ℕ} (e0 e1 : Bool) (w ih : ℕ) (out : List Bool)
    (hih : ih ≤ x.length + 1) (hw : 2 ≤ w) (hb : 2 * w < B) :
    Eval x B (termP e0 e1) ⟨ih, 0, Rl w, out⟩
      ⟨ih, 0, Rl w, out ++ ([e0, e1] ++ List.replicate (w - 2) false)⟩ := by
  have a1 := Eval.act' (x := x) (B := B) (T := Rl w) (out := out) (ih := ih) (wh := 0)
    none .stay .stay (some e0) (by simpa [Move.apply] using hih) (by simp [Move.apply]; omega)
  simp only [Move.apply, Option.getD_none, Function.update_eq_self, Option.toList_some] at a1
  have g1 := Eval.goR' (x := x) (B := B) (ih := ih) (T := Rl w) (out := out ++ [e0]) hih 2 0 (by omega)
  have a2 := Eval.act' (x := x) (B := B) (T := Rl w) (out := out ++ [e0]) (ih := ih) (wh := 0 + 2)
    none .stay .stay (some e1) (by simpa [Move.apply] using hih) (by simp [Move.apply]; omega)
  simp only [Move.apply, Option.getD_none, Function.update_eq_self, Option.toList_some] at a2
  have g2 := Eval.goR' (x := x) (B := B) (ih := ih) (T := Rl w) (out := out ++ [e0] ++ [e1]) hih 2 (0 + 2) (by omega)
  have t := tailLoop_spec (x := x) (B := B) w ih hih hb (w - 2) 2 (out ++ [e0] ++ [e1]) (by omega)
  have h := Eval.home' (x := x) (B := B) (ih := ih) (T := Rl w) (out := out ++ [e0] ++ [e1] ++ List.replicate (w - 2) false)
    hih (2 * w) hb
  simp only [Nat.zero_add] at g1 a2 g2
  rw [show 2 + 2 = 2 * 2 by omega] at g2
  have := Eval.seq a1 (Eval.seq g1 (Eval.seq a2 (Eval.seq g2 (Eval.seq t h))))
  simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] at this ⊢
  unfold termP
  exact this
/-! ### number theory and code words -/

def bl (n : ℕ) : ℕ := Nat.log 2 (n + 1) + 1

lemma natCode_eq (n : ℕ) : natCode n = List.replicate (bl n) true ++ [false] ++ bits (bl n) n := rfl

def Code (x : List Bool) (p n : ℕ) : Prop :=
  (∀ i < bl n, x[p + i]? = some true) ∧ x[p + bl n]? = some false ∧
  (∀ i < bl n, x[p + bl n + 1 + i]? = some (n.testBit i)) ∧ p + 2 * bl n + 1 ≤ x.length

lemma Code_of (pre rest : List Bool) (n : ℕ) :
    Code (pre ++ (natCode n ++ rest)) pre.length n := by
  have hl : (natCode n).length = 2 * bl n + 1 := by
    simp [natCode_eq, bits]; omega
  refine ⟨fun i hi => ?_, ?_, fun i hi => ?_, ?_⟩
  · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    simp [natCode_eq, List.getElem?_append, bits, List.getElem?_replicate, hi]
  · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    simp [natCode_eq, List.getElem?_append, bits, List.getElem?_replicate]
  · rw [List.getElem?_append_right (by omega), show pre.length + bl n + 1 + i - pre.length = bl n + 1 + i by omega]
    simp [natCode_eq, List.getElem?_append, bits, List.getElem?_replicate, hi]
    have : ¬ (bl n + 1 + i < bl n) := by omega
    have h2 : ¬ (bl n + 1 + i < bl n + 1) := by omega
    simp [this, h2, hi]
    rw [show bl n + 1 + i - bl n = i + 1 by omega]
    simp [List.getElem?_append, hi]
  · simp; omega

lemma Code_pat {x : List Bool} {p n : ℕ} (h : Code x p n) :
    decide (x[p]? = some true ∧ x[p + 1]? = some false ∧ x[p + 2]? = some false) = decide (n = 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  by_cases hn : n = 0
  · subst hn
    have hb : bl 0 = 1 := by simp [bl]
    have a1 := h1 0 (by omega)
    have a2 := h2
    have a3 := h3 0 (by omega)
    simp only [hb] at a1 a2 a3
    simp at a1 a2 a3
    simp [a1, a2, a3]
  · have hb : 2 ≤ bl n := by
      have : 1 ≤ Nat.log 2 (n + 1) := Nat.log_pos (by norm_num) (by omega)
      unfold bl; omega
    have a1 := h1 1 (by omega)
    simp [hn, a1]

lemma bits_eq_range (w n : ℕ) : bits w n = (List.range w).map n.testBit := rfl

lemma bits_shift {w j : ℕ} (hj : bl j ≤ w) :
    (List.range w).map (fun i => if i < bl j then j.testBit i else false) = bits w j := by
  rw [bits_eq_range]
  apply List.map_congr_left
  intro i hi
  by_cases h : i < bl j
  · simp [h]
  · simp only [h, if_false]
    symm
    apply Nat.testBit_eq_false_of_lt
    have : j + 1 < 2 ^ (Nat.log 2 (j + 1)).succ := Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : 2 ^ (Nat.log 2 (j + 1)).succ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by unfold bl at h; omega)
    omega

def vv (jz zz : Bool) : ℕ := (if zz then 0 else 1) + (if jz then 1 else 0)

lemma bits_term {w : ℕ} (hw : 2 ≤ w) (v : ℕ) (hv : v < 4) :
    bits w v = [v.testBit 0, v.testBit 1] ++ List.replicate (w - 2) false := by
  rw [bits_eq_range]
  apply List.ext_getElem?
  intro i
  rcases i with _ | _ | i
  · rw [List.getElem?_map, List.getElem?_range (by omega)]; simp
  · rw [List.getElem?_map, List.getElem?_range (by omega)]; simp
  · by_cases h : i + 2 < w
    · have : v.testBit (i + 2) = false := Nat.testBit_eq_false_of_lt (by
        calc v < 4 := hv
          _ = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (i + 2) := Nat.pow_le_pow_right (by norm_num) (by omega))
      simp [List.getElem?_range, List.getElem?_replicate, h, this, show i < w - 2 by omega]
    · simp [List.getElem?_range, List.getElem?_replicate, h, show ¬ i < w - 2 by omega]

lemma w_facts (m : ℕ) (hm : 3 ≤ m) (ho : m % 2 = 1) :
    (if m.testBit (bl m - 1) = false then bl m - 1 else bl m) = Nat.log 2 (m - 1) + 1 ∧
    ∀ j < m, bl j ≤ Nat.log 2 (m - 1) + 1 := by
  have h1 : 2 ^ Nat.log 2 (m + 1) ≤ m + 1 := Nat.pow_log_le_self 2 (by omega)
  have h2 : m + 1 < 2 ^ (Nat.log 2 (m + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hk2 : 2 ≤ Nat.log 2 (m + 1) := by
    by_contra hc
    have : 2 ^ (Nat.log 2 (m + 1) + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨k', hk'⟩ : ∃ k', Nat.log 2 (m + 1) = k' + 2 := ⟨Nat.log 2 (m + 1) - 2, by omega⟩
  have hbl : bl m = k' + 3 := by unfold bl; omega
  rw [hk'] at h1 h2
  constructor
  · rw [hbl, show k' + 3 - 1 = k' + 2 from rfl]
    have hp : 2 ^ (k' + 2) = 4 * 2 ^ k' := by ring
    have hp1 : 2 ^ (k' + 2 + 1) = 8 * 2 ^ k' := by ring
    have hp2 : 1 ≤ 2 ^ k' := Nat.one_le_two_pow
    by_cases ht : m.testBit (k' + 2) = false
    · simp only [ht, if_true]
      have hlt : m < 2 ^ (k' + 2) := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        rcases Nat.eq_or_lt_of_le hi with rfl | hi'
        · exact ht
        · apply Nat.testBit_eq_false_of_lt
          have : 2 ^ (k' + 2 + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi'
          omega
      have : Nat.log 2 (m - 1) = k' + 1 := by
        apply Nat.log_eq_of_pow_le_of_lt_pow
        · have : 2 ^ (k' + 1) = 2 * 2 ^ k' := by ring
          omega
        · have : 2 ^ (k' + 1 + 1) = 4 * 2 ^ k' := by ring
          omega
      omega
    · have ht' : m.testBit (k' + 2) = true := by simpa using ht
      have hge := Nat.ge_two_pow_of_testBit ht'
      have : Nat.log 2 (m - 1) = k' + 2 := by
        apply Nat.log_eq_of_pow_le_of_lt_pow
        · omega
        · omega
      simp [ht, this]
  · intro j hj
    have h3 : m - 1 < 2 ^ (Nat.log 2 (m - 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hp : 2 ^ (Nat.log 2 (m - 1) + 1) = 2 * 2 ^ Nat.log 2 (m - 1) := by ring
    have : Nat.log 2 (j + 1) < Nat.log 2 (m - 1) + 1 :=
      Nat.log_lt_of_lt_pow (by omega) (by omega)
    unfold bl; omega

/-! ### the whole program -/

def mainP : Prog :=
  .seq mvI (.seq skipP (.seq readP (.seq (goI 5)
    (pat (fun jz => .seq jP (pat (fun zz =>
      termP ((vv jz zz).testBit 0) ((vv jz zz).testBit 1))))))))

lemma natCode_len (n : ℕ) : (natCode n).length = 2 * bl n + 1 := by
  simp [natCode_eq, bits]; omega

lemma natCode_two : (natCode 2).length = 5 := by
  rw [natCode_len]
  have : bl 2 = 2 := by
    unfold bl
    have : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    simp [this]
  omega

lemma bl_pos (n : ℕ) : 1 ≤ bl n := by unfold bl; omega

lemma bl_le (b : ℕ) : bl (2 * b + 1) ≤ b + 2 := by
  unfold bl
  have h1 : b < 2 ^ b := Nat.lt_two_pow_self
  have h2 : 2 ^ (b + 2) = 4 * 2 ^ b := by ring
  have : Nat.log 2 (2 * b + 1 + 1) < b + 2 := Nat.log_lt_of_lt_pow (by omega) (by omega)
  omega

lemma main_eval (m j z : ℕ) (hm : 3 ≤ m) (ho : m % 2 = 1) (hj : j < m) (x : List Bool)
    (hx : x = natCode (natCode m).length ++ (natCode m ++ (natCode 2 ++ (natCode j ++ natCode z)))) :
    ∃ s' : St, Eval x (2 * bl m + 6) mainP ⟨0, 0, fun _ => false, []⟩ s' ∧
      s'.out = bits (Nat.log 2 (m - 1) + 1) j ++
        bits (Nat.log 2 (m - 1) + 1) (vv (decide (j = 0)) (decide (z = 0))) := by
  obtain ⟨hw1, hw2⟩ := w_facts m hm ho
  set w := Nat.log 2 (m - 1) + 1 with hwdef
  have hw2' : 2 ≤ w := by
    have : 1 ≤ Nat.log 2 (m - 1) := Nat.log_pos (by norm_num) (by omega)
    omega
  have hbm : bl m ≥ 3 := by
    have : 2 ≤ Nat.log 2 (m + 1) := by
      have h2 : m + 1 < 2 ^ (Nat.log 2 (m + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      by_contra hc
      have : 2 ^ (Nat.log 2 (m + 1) + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    unfold bl; omega
  have hwb : w ≤ bl m := by
    rw [← hw1]; split_ifs <;> omega
  -- code words
  have hLm := natCode_len m
  obtain ⟨L, hL⟩ : ∃ L, L = (natCode m).length := ⟨_, rfl⟩
  rw [← hL] at hx
  have hLb : bl L ≤ bl m + 2 := by rw [hL, hLm]; exact bl_le _
  have C1 : Code x 0 L := by
    have := Code_of [] (natCode m ++ (natCode 2 ++ (natCode j ++ natCode z))) L
    rw [hx]; simpa using this
  have C2 : Code x (natCode L).length m := by
    have := Code_of (natCode L) (natCode 2 ++ (natCode j ++ natCode z)) m
    rw [hx]; simpa [List.append_assoc] using this
  have C3 : Code x ((natCode L).length + (natCode m).length + 5) j := by
    have := Code_of (natCode L ++ natCode m ++ natCode 2) (natCode z) j
    rw [hx]
    simp only [List.length_append, natCode_two] at this
    simpa [List.append_assoc] using this
  have C4 : Code x ((natCode L).length + (natCode m).length + 5 + (natCode j).length) z := by
    have := Code_of (natCode L ++ natCode m ++ natCode 2 ++ natCode j) [] z
    rw [hx]
    simp only [List.length_append, natCode_two] at this
    simpa [List.append_assoc, Nat.add_assoc] using this
  rw [natCode_len L] at C2 C3 C4
  rw [hLm] at C3 C4
  rw [natCode_len j] at C4
  set bL := bl L with hbL
  set bj := bl j with hbj
  set bm := bl m with hbm'
  have hbj1 := bl_pos j
  have hbjw : bj ≤ w := hw2 j hj
  have hB : 0 < 2 * bm + 6 := by omega
  -- step 1: skip L
  have e0 := Eval.mvI' (x := x) (B := 2 * bm + 6) (ih := 0) (wh := 0) (T := fun _ => false) (out := [])
    (by have := C1.2.2.2; omega) hB
  have e1 := skipP_spec (x := x) (B := 2 * bm + 6) bL 1 [] le_rfl
    (fun i hi => by simpa using C1.1 i hi) (by simpa using C1.2.1)
    (by have := C1.2.2.2; omega) (by omega)
  -- step 2: read m
  have e2 := readP_spec (x := x) (B := 2 * bm + 6) bm (1 + 2 * bL + 1) [] (by omega) (by omega)
    (fun i hi => by have := C2.1 i hi; rwa [show 1 + 2 * bL + 1 - 1 + i = 2 * bL + 1 + i by omega])
    (by have := C2.2.1; rwa [show 1 + 2 * bL + 1 - 1 + bm = 2 * bL + 1 + bm by omega])
    (by have := C2.2.2.2; omega) (by omega)
  have hlast : (if x[1 + 2 * bL + 1 + 2 * bm - 1]? = some false then bm - 1 else bm) = w := by
    have := C2.2.2.1 (bm - 1) (by omega)
    rw [show 2 * bL + 1 + bm + 1 + (bm - 1) = 1 + 2 * bL + 1 + 2 * bm - 1 by omega] at this
    rw [this, ← hw1]
    by_cases h : m.testBit (bm - 1) = false <;> simp [h]
  rw [hlast] at e2
  -- step 3: skip the fixed header
  have e3 := goI_spec (x := x) (B := 2 * bm + 6) (wh := 0) (T := Rl w) (out := []) hB 5
    (1 + 2 * bL + 1 + 2 * bm + 1) (by have := C3.2.2.2; omega)
  -- step 4: pattern for j
  obtain ⟨p4, hp4⟩ : ∃ p4, p4 = 2 * bL + 1 + (2 * bm + 1) + 5 := ⟨_, rfl⟩
  obtain ⟨p5, hp5⟩ : ∃ p5, p5 = p4 + (2 * bj + 1) := ⟨_, rfl⟩
  have C3' : Code x p4 j := by rw [hp4]; exact C3
  have C4' : Code x p5 z := by rw [hp5, hp4]; exact C4
  have hbz := bl_pos z
  have hih4 : 1 + 2 * bL + 1 + 2 * bm + 1 + 5 = p4 + 1 := by omega
  rw [hih4] at e3
  have hpj : decide (x[p4 + 1 - 1]? = some true ∧ x[p4 + 1]? = some false ∧ x[p4 + 1 + 1]? = some false)
      = decide (j = 0) := by simpa using Code_pat C3'
  have hpz : decide (x[p5 + 1 - 1]? = some true ∧ x[p5 + 1]? = some false ∧ x[p5 + 1 + 1]? = some false)
      = decide (z = 0) := by simpa using Code_pat C4'
  have jE := jP_spec (x := x) (B := 2 * bm + 6) j.testBit w bj (p4 + 1) [] hbjw (by omega)
    (fun i hi => by simpa using C3'.1 i hi) (by simpa using C3'.2.1)
    (fun i hi => by
      have := C3'.2.2.1 i hi
      rwa [show p4 + bj + 1 + i = p4 + 1 + bj + i by omega] at this)
    (by have := C3'.2.2.2; omega) (by omega)
  rw [show p4 + 1 + 2 * bj + 1 = p5 + 1 by omega] at jE
  have tE := termP_spec (x := x) (B := 2 * bm + 6)
    ((vv (decide (j = 0)) (decide (z = 0))).testBit 0) ((vv (decide (j = 0)) (decide (z = 0))).testBit 1)
    w (p5 + 1) ([] ++ (List.range w).map (fun i => if i < bj then j.testBit i else false))
    (by have := C4'.2.2.2; omega) hw2' (by omega)
  have zE : Eval x (2 * bm + 6) (pat (fun zz =>
      termP ((vv (decide (j = 0)) zz).testBit 0) ((vv (decide (j = 0)) zz).testBit 1)))
      ⟨p5 + 1, 0, Rl w, [] ++ (List.range w).map (fun i => if i < bj then j.testBit i else false)⟩
      ⟨p5 + 1, 0, Rl w, [] ++ (List.range w).map (fun i => if i < bj then j.testBit i else false) ++
        ([(vv (decide (j = 0)) (decide (z = 0))).testBit 0, (vv (decide (j = 0)) (decide (z = 0))).testBit 1] ++
          List.replicate (w - 2) false)⟩ := by
    refine pat_spec _ (by omega) (by have := C4'.2.2.2; omega) hB ?_
    beta_reduce
    rw [hpz]
    exact tE
  have jzE : Eval x (2 * bm + 6) (pat (fun jz => .seq jP (pat (fun zz =>
      termP ((vv jz zz).testBit 0) ((vv jz zz).testBit 1)))))
      ⟨p4 + 1, 0, Rl w, []⟩
      ⟨p5 + 1, 0, Rl w, [] ++ (List.range w).map (fun i => if i < bj then j.testBit i else false) ++
        ([(vv (decide (j = 0)) (decide (z = 0))).testBit 0, (vv (decide (j = 0)) (decide (z = 0))).testBit 1] ++
          List.replicate (w - 2) false)⟩ := by
    refine pat_spec _ (by omega) (by have := C3'.2.2.2; omega) hB ?_
    beta_reduce
    rw [hpj]
    exact Eval.seq jE zE
  have E := Eval.seq e0 (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 jzE)))
  refine ⟨_, E, ?_⟩
  · simp only [List.nil_append]
    rw [bits_shift hbjw, ← bits_term hw2' _ (by unfold vv; split_ifs <;> simp)]

/-! ### the decoder -/

lemma bl_ge3 (m : ℕ) (hm : 3 ≤ m) : 3 ≤ bl m := by
  have h2 : m + 1 < 2 ^ (Nat.log 2 (m + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have : 2 ≤ Nat.log 2 (m + 1) := by
    by_contra hc
    have : 2 ^ (Nat.log 2 (m + 1) + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  unfold bl; omega

def dec (m : ℕ) : Decoder m m where
  shift j := ((j : ℕ) : ZMod m)
  term j y := ((vv (decide ((j : ℕ) = 0)) (decide (y.val = 0)) : ℕ) : ZMod m)

lemma term_eq {m : ℕ} (j : Fin m) (y : ZMod m) :
    (dec m).term j y = (if y = 0 then 0 else 1) + (if (j : ℕ) = 0 then 1 else 0) := by
  simp only [dec, vv, ZMod.val_eq_zero, decide_eq_true_eq]
  by_cases h1 : y = 0 <;> by_cases h2 : (j : ℕ) = 0 <;> simp [h1, h2] <;> norm_num

lemma sum_nonzero (m : ℕ) [NeZero m] :
    ∑ y : ZMod m, (if y = 0 then (0 : ZMod m) else 1) = -1 := by
  have h : ∑ y : ZMod m, ((if y = 0 then (0 : ZMod m) else 1) + (if y = 0 then 1 else 0)) =
      ∑ _y : ZMod m, (1 : ZMod m) := by
    apply Finset.sum_congr rfl; intro y _; by_cases hy : y = 0 <;> simp [hy]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (0 : ZMod m) (fun _ => (1 : ZMod m))] at h
  simp only [Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    mul_one, ZMod.natCast_self] at h
  linear_combination h

lemma sum_zero_idx (m : ℕ) [NeZero m] :
    ∑ j : Fin m, (if (j : ℕ) = 0 then (1 : ZMod m) else 0) = 1 := by
  rw [Finset.sum_eq_single_of_mem (⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩ : Fin m) (Finset.mem_univ _)]
  · simp
  · intro j _ hj
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    simp [this]

lemma isDecoder_dec (m : ℕ) [Fact m.Prime] : IsDecoder Set.univ (dec m) := by
  have : NeZero m := ⟨(Fact.out : m.Prime).ne_zero⟩
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · intro a _ ha z
    have hbij : Function.Bijective (fun j : Fin m => z + a * ((j : ℕ) : ZMod m)) := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨?_, by simp [ZMod.card]⟩
      intro i k hik
      have h1 : a * ((i : ℕ) : ZMod m) = a * ((k : ℕ) : ZMod m) := add_left_cancel hik
      have h2 := mul_left_cancel₀ ha h1
      apply Fin.ext
      have := congrArg ZMod.val h2
      rwa [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt k.isLt] at this
    have hh : ∀ j : Fin m, (dec m).term j (z + a * (dec m).shift j) =
        (if z + a * ((j : ℕ) : ZMod m) = 0 then (0 : ZMod m) else 1) + (if (j : ℕ) = 0 then 1 else 0) :=
      fun j => term_eq j _
    rw [Finset.sum_congr rfl (fun j _ => hh j), Finset.sum_add_distrib, sum_zero_idx]
    rw [Fintype.sum_bijective _ hbij (fun j : Fin m => (if z + a * ((j : ℕ) : ZMod m) = 0 then (0 : ZMod m) else 1))
      (fun y : ZMod m => (if y = 0 then (0 : ZMod m) else 1)) (fun _ => rfl), sum_nonzero]
    simp
  · simp only [term_eq, Finset.sum_add_distrib, sum_zero_idx]
    simp

/-! ### final -/

lemma bl_le_lg (m : ℕ) : (bl m : ℝ) ≤ lg m := by
  have := natLog_le_logb (m + 1) (by omega)
  unfold bl lg log₂
  have h : Real.logb 2 ((m : ℝ) + 1) = Real.log ((m : ℝ) + 1) / Real.log 2 := rfl
  push_cast at this ⊢
  rw [h] at this
  linarith

theorem lemma_3_20 :
    ∃ (MD : Machine) (C : ℝ), 0 < C ∧
      ∀ m : ℕ, Nat.Prime m → Odd m → ∃ k : ℕ, k ≤ m ∧
      ∃ D : Decoder m k, IsDecoder Set.univ D ∧
        DecoderAccess MD (natCode m) D (C * lg m) := by
  refine ⟨toMachine (mainP.comp 0), 4, by norm_num, ?_⟩
  intro m hp hodd
  have hm : 3 ≤ m := by
    have := hp.two_le
    obtain ⟨t, ht⟩ := hodd
    omega
  have ho : m % 2 = 1 := Nat.odd_iff.mp hodd
  haveI : Fact m.Prime := ⟨hp⟩
  refine ⟨m, le_rfl, dec m, isDecoder_dec m, ?_⟩
  intro j z
  have hj := j.isLt
  have hv : vv (decide ((j : ℕ) = 0)) (decide (z.val = 0)) < m := by
    unfold vv; split_ifs <;> omega
  obtain ⟨s', hE, hout⟩ := main_eval m j z.val hm ho hj
    (decoderRequest (natCode m) j z.val)
    (by simp [decoderRequest, listCode, natsCode, List.append_assoc])
  have hs : ((dec m).shift j).val = j := by
    simp only [dec]; exact ZMod.val_natCast_of_lt hj
  have ht : ((dec m).term j z).val = vv (decide ((j : ℕ) = 0)) (decide (z.val = 0)) := by
    simp only [dec]; exact ZMod.val_natCast_of_lt hv
  rw [hs, ht]
  have hb3 := bl_ge3 m hm
  have hl := bl_le_lg m
  have hB : 2 * bl m + 6 ≤ ⌈(4 : ℝ) * lg m⌉₊ := by
    have h1 : ((2 * bl m + 6 : ℕ) : ℝ) ≤ 4 * lg m := by
      push_cast
      have : (3 : ℝ) ≤ bl m := by exact_mod_cast hb3
      linarith
    exact_mod_cast le_trans h1 (Nat.le_ceil _)
  exact prints_of_eval mainP _ _ (2 * bl m + 6) _ hB (by omega) s' hE hout

end CatalyticTreeEval.Main.Supplement

open CatalyticTreeEval.Main in
theorem solution :
    ∃ (MD : Machine) (C : ℝ), 0 < C ∧
      ∀ m : ℕ, Nat.Prime m → Odd m → ∃ k : ℕ, k ≤ m ∧
      ∃ D : Decoder m k, IsDecoder Set.univ D ∧
        DecoderAccess MD (natCode m) D (C * lg m) :=
  CatalyticTreeEval.Main.Supplement.lemma_3_20
