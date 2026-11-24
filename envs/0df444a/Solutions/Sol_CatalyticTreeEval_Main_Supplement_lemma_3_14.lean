-- Prove2me | solution 1 for CatalyticTreeEval.Main.Supplement.lemma_3_14
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T15:59:06.51482+00:00
-- url     : https://prove2.me/submissions/759eddbf-162b-4024-b748-8b8f095efc45

import Definitions.Def_CatalyticTreeEval_Main_Supplement_UniformConstructions

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

lemma exists_prime_Ioo (D : ℕ) (hD : 0 < D) : ∃ p, Nat.Prime p ∧ 2 * D < p ∧ p < 4 * D := by
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * D) (by omega)
  refine ⟨p, hp, h1, ?_⟩
  rcases h2.lt_or_eq with h | h
  · omega
  · exfalso
    have : 2 ∣ p := ⟨2 * D, by omega⟩
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this
    omega

lemma natLog_le_logb (n : ℕ) (hn : 0 < n) : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hn)]
  rw [Real.rpow_natCast]
  exact_mod_cast Nat.pow_log_le_self 2 hn.ne'


/-! ### Layer B: tape primitives -/

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


def Lane (T : ℕ → Bool) (ℓ c v : ℕ) : Prop := ∀ i, T (8 * (c + i) + ℓ) = v.testBit i

def incLoop : Prog :=
  .while (fun _ w _ _ => w) (.seq (.act (some false) .right .stay none) (goR 7))

lemma Eval.incLoop' {x B ih out} (ℓ : ℕ) (hℓ : ℓ < 8) (hih : ih ≤ x.length + 1) :
    ∀ (t c : ℕ) (T : ℕ → Bool), (∀ i < t, T (8 * (c + i) + ℓ) = true) →
      T (8 * (c + t) + ℓ) = false → 8 * (c + t) + ℓ < B →
      Eval x B incLoop ⟨ih, 8 * c + ℓ, T, out⟩
        ⟨ih, 8 * (c + t) + ℓ,
          fun a => if a % 8 = ℓ ∧ c ≤ a / 8 ∧ a / 8 < c + t then false else T a, out⟩
  | 0, c, T, _, hf, hb => by
    have : (fun a => if a % 8 = ℓ ∧ c ≤ a / 8 ∧ a / 8 < c + 0 then false else T a) = T := by
      funext a
      split_ifs with h
      · exfalso; omega
      · rfl
    rw [this]
    apply Eval.while_f
    simpa [St.test] using hf
  | t + 1, c, T, ht, hf, hb => by
    apply Eval.while_t (s1 := ⟨ih, 8 * (c + 1) + ℓ, Function.update T (8 * c + ℓ) false, out⟩)
    · simpa [St.test] using ht 0 (by omega)
    · have h1 := Eval.wrR (x := x) (B := B) (T := T) (out := out) (wh := 8 * c + ℓ) false .right hih
        (by simp only [Move.apply]; omega)
      have h2 := Eval.goR' (x := x) (B := B) (T := Function.update T (8 * c + ℓ) false) (out := out)
        hih 7 (Move.right.apply (8 * c + ℓ)) (by simp only [Move.apply]; omega)
      have := Eval.seq (p := .act (some false) .right .stay none) (q := goR 7) h1 h2
      simp only [Move.apply] at this
      rwa [show 8 * c + ℓ + 1 + 7 = 8 * (c + 1) + ℓ by ring] at this
    · have ih' := Eval.incLoop' (out := out) ℓ hℓ hih t (c + 1) (Function.update T (8 * c + ℓ) false)
        (by
          intro i hi
          rw [Function.update_of_ne (by omega)]
          have := ht (i + 1) (by omega)
          rwa [show c + (i + 1) = c + 1 + i by ring] at this)
        (by
          rw [Function.update_of_ne (by omega)]
          rwa [show c + 1 + t = c + (t + 1) by ring])
        (by rw [show c + 1 + t = c + (t + 1) by ring]; exact hb)
      rw [show c + 1 + t = c + (t + 1) by ring] at ih'
      have e : (fun a => if a % 8 = ℓ ∧ c + 1 ≤ a / 8 ∧ a / 8 < c + (t + 1) then false
          else Function.update T (8 * c + ℓ) false a) =
          (fun a => if a % 8 = ℓ ∧ c ≤ a / 8 ∧ a / 8 < c + (t + 1) then false else T a) := by
        funext a
        by_cases ha : a = 8 * c + ℓ
        · subst ha
          have h1 : (8 * c + ℓ) % 8 = ℓ := by omega
          have h2 : (8 * c + ℓ) / 8 = c := by omega
          simp [h1, h2]
        · rw [Function.update_of_ne ha]
          by_cases h : a % 8 = ℓ ∧ c ≤ a / 8 ∧ a / 8 < c + (t + 1)
          · have : c + 1 ≤ a / 8 := by
              by_contra hc
              apply ha
              omega
            rw [if_pos h, if_pos ⟨h.1, this, h.2.2⟩]
          · have h2 : ¬(a % 8 = ℓ ∧ c + 1 ≤ a / 8 ∧ a / 8 < c + (t + 1)) :=
              fun h' => h ⟨h'.1, by omega, h'.2.2⟩
            rw [if_neg h, if_neg h2]
      rw [e] at ih'
      exact ih'

lemma succ_testBit : ∀ (t v : ℕ), (∀ i < t, v.testBit i = true) → v.testBit t = false → ∀ i,
    (v + 1).testBit i = if i < t then false else if i = t then true else v.testBit i
  | 0, v, _, h2, i => by
    have hv : v % 2 = 0 := by simpa [Nat.testBit_zero] using h2
    rcases i with _ | j
    · simp [Nat.testBit_zero]; omega
    · rw [Nat.testBit_succ, Nat.testBit_succ]
      have : (v + 1) / 2 = v / 2 := by omega
      simp [this]
  | t + 1, v, h1, h2, i => by
    have hv : v % 2 = 1 := by simpa [Nat.testBit_zero] using h1 0 (by omega)
    rcases i with _ | j
    · have : (v + 1) % 2 = 0 := by omega
      simp [Nat.testBit_zero, this]
    · rw [Nat.testBit_succ, show (v + 1) / 2 = v / 2 + 1 by omega]
      have := succ_testBit t (v / 2) (fun i hi => by
        have := h1 (i + 1) (by omega); rwa [Nat.testBit_succ] at this)
        (by have := h2; rwa [Nat.testBit_succ] at this) j
      rw [this, Nat.testBit_succ]
      by_cases a : j < t
      · simp [a]
      · by_cases b : j = t
        · simp [b]
        · simp [a, b]

lemma two_pow_le_of_testBit : ∀ (w v : ℕ), (∀ i < w, v.testBit i = true) → 2 ^ w ≤ v + 1
  | 0, v, _ => by simp
  | w + 1, v, h => by
    have hv : v % 2 = 1 := by simpa [Nat.testBit_zero] using h 0 (by omega)
    have := two_pow_le_of_testBit w (v / 2) (fun i hi => by
      have := h (i + 1) (by omega); rwa [Nat.testBit_succ] at this)
    rw [pow_succ]; omega

def incP (ℓ : ℕ) : Prog :=
  .seq (goR ℓ) (.seq incLoop (.seq (.act (some true) .stay .stay none) home))

lemma inc_spec {x B ih out} (ℓ : ℕ) (hℓ : ℓ < 8) (hih : ih ≤ x.length + 1) (T : ℕ → Bool)
    (v w : ℕ) (hL : Lane T ℓ 0 v) (hv : v + 1 < 2 ^ w) (hB : 8 * w + 8 ≤ B) :
    ∃ T', Eval x B (incP ℓ) ⟨ih, 0, T, out⟩ ⟨ih, 0, T', out⟩ ∧ Lane T' ℓ 0 (v + 1) ∧
      ∀ a, a % 8 ≠ ℓ → T' a = T a := by
  have hex : ∃ i, v.testBit i = false := ⟨v, Nat.testBit_eq_false_of_lt (Nat.lt_two_pow_self)⟩
  classical
  set t := Nat.find hex with ht
  have ht1 : ∀ i < t, v.testBit i = true := by
    intro i hi
    have := Nat.find_min hex hi
    simpa using this
  have ht2 : v.testBit t = false := Nat.find_spec hex
  have htw : t < w := by
    by_contra hc
    have := two_pow_le_of_testBit w v (fun i hi => ht1 i (by omega))
    omega
  have hA : 0 + ℓ < B := by omega
  have e1 := Eval.goR' (x := x) (B := B) (T := T) (out := out) hih ℓ 0 (by omega)
  have e2 := Eval.incLoop' (x := x) (B := B) (out := out) ℓ hℓ hih t 0 T
    (fun i hi => by rw [hL i]; exact ht1 i hi)
    (by rw [hL t]; exact ht2) (by omega)
  set T1 : ℕ → Bool := fun a => if a % 8 = ℓ ∧ 0 ≤ a / 8 ∧ a / 8 < 0 + t then false else T a with hT1
  have e3 := Eval.wrR (x := x) (B := B) (T := T1) (out := out) (wh := 8 * (0 + t) + ℓ) true .stay hih
    (by simp only [Move.apply]; omega)
  have e4 := Eval.home' (x := x) (B := B) (T := Function.update T1 (8 * (0 + t) + ℓ) true) (out := out)
    hih (Move.stay.apply (8 * (0 + t) + ℓ)) (by simp only [Move.apply]; omega)
  refine ⟨Function.update T1 (8 * (0 + t) + ℓ) true, ?_, ?_, ?_⟩
  · simp only [Nat.zero_add] at e1
    rw [show 8 * 0 + ℓ = ℓ by ring] at e2
    exact Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))
  · intro i
    rw [succ_testBit t v ht1 ht2 i]
    by_cases a : i < t
    · rw [Function.update_of_ne (by omega)]
      simp only [hT1]
      have h1 : (8 * (0 + i) + ℓ) % 8 = ℓ := by omega
      have h2 : (8 * (0 + i) + ℓ) / 8 = 0 + i := by omega
      rw [if_pos ⟨h1, by omega, by omega⟩, if_pos a]
    · rw [if_neg a]
      by_cases b : i = t
      · subst b
        simp
      · rw [if_neg b, Function.update_of_ne (by omega)]
        simp only [hT1]
        have h1 : (8 * (0 + i) + ℓ) % 8 = ℓ := by omega
        have h2 : (8 * (0 + i) + ℓ) / 8 = 0 + i := by omega
        rw [if_neg (by omega), hL i]
  · intro a ha
    rw [Function.update_of_ne (by omega)]
    simp only [hT1]
    rw [if_neg (fun h => ha h.1)]



/-! ### Layer C: column operations and the register encoding -/

def goL : ℕ → Prog
  | 0 => .skip
  | n + 1 => .seq mvL (goL n)

lemma Eval.goL' {x B ih T out} (hih : ih ≤ x.length + 1) :
    ∀ (n wh : ℕ), wh < B → Eval x B (goL n) ⟨ih, wh, T, out⟩ ⟨ih, wh - n, T, out⟩
  | 0, wh, _ => by simpa [goL] using (Eval.skip : Eval x B .skip ⟨ih, wh, T, out⟩ _)
  | n + 1, wh, hb => by
    have h1 := Eval.mvL' (x := x) (B := B) (T := T) (out := out) (wh := wh) hih hb
    have h2 := Eval.goL' (x := x) (B := B) (T := T) (out := out) hih n (wh - 1) (by omega)
    rw [show wh - (n + 1) = wh - 1 - n by omega]
    exact Eval.seq (p := mvL) (q := goL n) h1 h2

def rd (k : Bool → Prog) : Prog := .ite (fun _ w _ _ => w) (k true) (k false)

lemma Eval.rd' {x B} (k : Bool → Prog) {ih wh T out} {s' : St}
    (h : Eval x B (k (T wh)) ⟨ih, wh, T, out⟩ s') : Eval x B (rd k) ⟨ih, wh, T, out⟩ s' := by
  unfold rd
  cases hT : T wh
  · rw [hT] at h; exact Eval.ite_f (by simp [St.test, hT]) h
  · rw [hT] at h; exact Eval.ite_t (by simp [St.test, hT]) h

def wrMv (b : Bool) : Prog := .act (some b) .right .stay none

def colOp (a b t : ℕ) (f : Bool → Bool → Bool) : Prog :=
  .seq (goR a) (rd fun u => .seq (goR (b - a)) (rd fun v =>
    .seq (goR (t - b)) (.seq (wrMv (f u v)) (goR (7 - t)))))

lemma colOp_spec {x B ih out} (a b t : ℕ) (f : Bool → Bool → Bool) (hab : a ≤ b) (hbt : b ≤ t)
    (ht : t < 8) (hih : ih ≤ x.length + 1) (c : ℕ) (T : ℕ → Bool) (hB : 8 * c + 8 < B) :
    Eval x B (colOp a b t f) ⟨ih, 8 * c, T, out⟩
      ⟨ih, 8 * c + 8, Function.update T (8 * c + t) (f (T (8 * c + a)) (T (8 * c + b))), out⟩ := by
  unfold colOp
  refine Eval.seq (Eval.goR' (x := x) (B := B) (T := T) (out := out) hih a (8 * c) (by omega)) ?_
  apply Eval.rd'
  try dsimp only
  refine Eval.seq (Eval.goR' (x := x) (B := B) (T := T) (out := out) hih (b - a) (8 * c + a)
    (by omega)) ?_
  apply Eval.rd'
  try dsimp only
  refine Eval.seq (Eval.goR' (x := x) (B := B) (T := T) (out := out) hih (t - b)
    (8 * c + a + (b - a)) (by omega)) ?_
  have e1 : 8 * c + a + (b - a) = 8 * c + b := by omega
  have e2 : 8 * c + b + (t - b) = 8 * c + t := by omega
  rw [e1, e2]
  have h1 := Eval.wrR (x := x) (B := B) (T := T) (out := out) (wh := 8 * c + t)
    (f (T (8 * c + a)) (T (8 * c + b))) .right hih (by simp only [Move.apply]; omega)
  have h2 := Eval.goR' (x := x) (B := B)
    (T := Function.update T (8 * c + t) (f (T (8 * c + a)) (T (8 * c + b)))) (out := out) hih
    (7 - t) (8 * c + t + 1) (by omega)
  simp only [Move.apply] at h1
  rw [show 8 * c + t + 1 + (7 - t) = 8 * c + 8 by omega] at h2
  exact Eval.seq (p := wrMv _) h1 h2

def sweep (P : Prog) : Prog := .while (fun _ w _ _ => w) P

lemma sweep_spec {x B ih out} (a b t : ℕ) (f : Bool → Bool → Bool) (hab : a ≤ b) (hbt : b ≤ t)
    (ht : t < 8) (ht0 : 0 < t) (hih : ih ≤ x.length + 1) :
    ∀ (n c : ℕ) (T : ℕ → Bool), (∀ i < n, T (8 * (c + i)) = true) → T (8 * (c + n)) = false →
      8 * (c + n) < B →
      Eval x B (sweep (colOp a b t f)) ⟨ih, 8 * c, T, out⟩
        ⟨ih, 8 * (c + n), fun z => if z % 8 = t ∧ c ≤ z / 8 ∧ z / 8 < c + n then
            f (T (8 * (z / 8) + a)) (T (8 * (z / 8) + b)) else T z, out⟩
  | 0, c, T, _, hf, hb => by
    have : (fun z => if z % 8 = t ∧ c ≤ z / 8 ∧ z / 8 < c + 0 then
        f (T (8 * (z / 8) + a)) (T (8 * (z / 8) + b)) else T z) = T := by
      funext z
      rw [if_neg (by omega)]
    rw [this]
    apply Eval.while_f
    simpa [St.test] using hf
  | n + 1, c, T, ht1, hf, hb => by
    have e0 := colOp_spec (x := x) (B := B) (out := out) a b t f hab hbt ht hih c T (by omega)
    rw [show 8 * c + 8 = 8 * (c + 1) by ring] at e0
    set T' := Function.update T (8 * c + t) (f (T (8 * c + a)) (T (8 * c + b))) with hT'
    have ih' := sweep_spec (out := out) a b t f hab hbt ht ht0 hih n (c + 1) T'
      (by
        intro i hi
        rw [hT', Function.update_of_ne (by omega)]
        have := ht1 (i + 1) (by omega)
        rwa [show c + (i + 1) = c + 1 + i by ring] at this)
      (by
        rw [hT', Function.update_of_ne (by omega)]
        rwa [show c + 1 + n = c + (n + 1) by ring])
      (by rw [show c + 1 + n = c + (n + 1) by ring]; exact hb)
    rw [show c + 1 + n = c + (n + 1) by ring] at ih'
    have e : (fun z => if z % 8 = t ∧ c + 1 ≤ z / 8 ∧ z / 8 < c + (n + 1) then
        f (T' (8 * (z / 8) + a)) (T' (8 * (z / 8) + b)) else T' z) =
        (fun z => if z % 8 = t ∧ c ≤ z / 8 ∧ z / 8 < c + (n + 1) then
          f (T (8 * (z / 8) + a)) (T (8 * (z / 8) + b)) else T z) := by
      funext z
      by_cases hz : z = 8 * c + t
      · subst hz
        have h1 : (8 * c + t) % 8 = t := by omega
        have h2 : (8 * c + t) / 8 = c := by omega
        simp [h1, h2, hT']
      · by_cases h : z % 8 = t ∧ c + 1 ≤ z / 8 ∧ z / 8 < c + (n + 1)
        · rw [if_pos h, if_pos ⟨h.1, by omega, h.2.2⟩, hT', Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
        · rw [if_neg h, if_neg (by omega), hT', Function.update_of_ne hz]
    rw [e] at ih'
    apply Eval.while_t (s1 := ⟨ih, 8 * (c + 1), T', out⟩)
    · simpa [St.test] using ht1 0 (by omega)
    · exact e0
    · exact ih'

def mapP (a b t : ℕ) (f : Bool → Bool → Bool) : Prog := .seq (sweep (colOp a b t f)) home

lemma mapP_eval {x B ih out} (a b t : ℕ) (f : Bool → Bool → Bool) (hab : a ≤ b) (hbt : b ≤ t)
    (ht : t < 8) (ht0 : 0 < t) (hih : ih ≤ x.length + 1) (w : ℕ) (T : ℕ → Bool)
    (hr : ∀ c, T (8 * c) = decide (c < w)) (hB : 8 * w + 8 ≤ B) :
    Eval x B (mapP a b t f) ⟨ih, 0, T, out⟩ ⟨ih, 0, fun z => if z % 8 = t ∧ z / 8 < w then
      f (T (8 * (z / 8) + a)) (T (8 * (z / 8) + b)) else T z, out⟩ := by
  have e1 := sweep_spec (x := x) (B := B) (out := out) a b t f hab hbt ht ht0 hih w 0 T
    (fun i hi => by rw [hr]; simp; omega) (by rw [hr]; simp) (by omega)
  simp only [zero_add, Nat.zero_le, true_and, mul_zero] at e1
  exact Eval.seq e1 (Eval.home' hih _ (by omega))

structure Enc (w : ℕ) (T : ℕ → Bool) (r : ℕ → ℕ) : Prop where
  ruler : ∀ c, T (8 * c) = decide (c < w)
  lanes : ∀ c j, 1 ≤ j → j ≤ 6 → T (8 * c + j) = (r j).testBit c
  scr : ∀ c, T (8 * c + 7) = false
  bd : ∀ j, 1 ≤ j → j ≤ 6 → r j < 2 ^ w

def RRun (x : List Bool) (B w : ℕ) (P : Prog) (r r' : ℕ → ℕ) : Prop :=
  ∀ ih T out, ih ≤ x.length + 1 → Enc w T r →
    ∃ T', Eval x B P ⟨ih, 0, T, out⟩ ⟨ih, 0, T', out⟩ ∧ Enc w T' r'

lemma RRun.seq {x B w P Q r r1 r2} (h1 : RRun x B w P r r1) (h2 : RRun x B w Q r1 r2) :
    RRun x B w (.seq P Q) r r2 := by
  intro ih T out hih hT
  obtain ⟨T1, e1, h1⟩ := h1 ih T out hih hT
  obtain ⟨T2, e2, h2⟩ := h2 ih T1 out hih h1
  exact ⟨T2, Eval.seq e1 e2, h2⟩

lemma RRun.skip {x B w r} : RRun x B w .skip r r :=
  fun _ T _ _ hT => ⟨T, Eval.skip, hT⟩

lemma md8 (c j : ℕ) (hj : j < 8) : (8 * c + j) % 8 = j := by omega
lemma dv8 (c j : ℕ) (hj : j < 8) : (8 * c + j) / 8 = c := by omega

lemma testBit_ge {v w c : ℕ} (h : v < 2 ^ w) (hc : w ≤ c) : v.testBit c = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hc))

lemma mapP_run {x B w} (a b t : ℕ) (f : Bool → Bool → Bool) (ha : 1 ≤ a) (hab : a ≤ b)
    (hbt : b ≤ t) (ht : t ≤ 6) (hB : 8 * w + 8 ≤ B) (r : ℕ → ℕ) (v : ℕ) (hv : v < 2 ^ w)
    (hf : ∀ c < w, f ((r a).testBit c) ((r b).testBit c) = v.testBit c) :
    RRun x B w (mapP a b t f) r (Function.update r t v) := by
  intro ih T out hih hT
  refine ⟨_, mapP_eval a b t f hab hbt (by omega) (by omega) hih w T hT.ruler hB, ?_⟩
  constructor
  · intro c
    have h1 : ¬((8 * c) % 8 = t ∧ (8 * c) / 8 < w) := by omega
    simp only [if_neg h1]
    exact hT.ruler c
  · intro c j hj1 hj6
    simp only [md8 c j (by omega), dv8 c j (by omega)]
    by_cases hjt : j = t
    · subst hjt
      simp only [true_and, Function.update_self]
      split_ifs with hc
      · rw [hT.lanes c a ha (by omega), hT.lanes c b (by omega) (by omega)]
        exact hf c hc
      · rw [hT.lanes c j hj1 hj6, testBit_ge (hT.bd j hj1 hj6) (by omega), testBit_ge hv (by omega)]
    · rw [if_neg (fun h => hjt h.1), Function.update_of_ne hjt]
      exact hT.lanes c j hj1 hj6
  · intro c
    simp only [md8 c 7 (by omega)]
    rw [if_neg (by omega)]
    exact hT.scr c
  · intro j hj1 hj6
    by_cases hjt : j = t
    · subst hjt; simpa using hv
    · rw [Function.update_of_ne hjt]; exact hT.bd j hj1 hj6

lemma inc_run {x B w} (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ6 : ℓ ≤ 6) (hB : 8 * w + 8 ≤ B) (r : ℕ → ℕ)
    (hv : r ℓ + 1 < 2 ^ w) : RRun x B w (incP ℓ) r (Function.update r ℓ (r ℓ + 1)) := by
  intro ih T out hih hT
  obtain ⟨T', e, hL, ho⟩ := inc_spec (x := x) (B := B) (out := out) ℓ (by omega) hih T (r ℓ) w
    (fun i => by simpa using hT.lanes i ℓ hℓ1 hℓ6) hv hB
  refine ⟨T', e, ?_, ?_, ?_, ?_⟩
  · intro c; rw [ho _ (by omega)]; exact hT.ruler c
  · intro c j hj1 hj6
    by_cases hjt : j = ℓ
    · subst hjt; simpa using hL c
    · rw [ho _ (by omega), Function.update_of_ne hjt]; exact hT.lanes c j hj1 hj6
  · intro c; rw [ho _ (by omega)]; exact hT.scr c
  · intro j hj1 hj6
    by_cases hjt : j = ℓ
    · subst hjt; simpa using hv
    · rw [Function.update_of_ne hjt]; exact hT.bd j hj1 hj6

/-! ### Tests, conditionals and loops on registers -/

def All (w : ℕ) (r : ℕ → ℕ) (a b : ℕ) (f : Bool → Bool → Bool) : Prop :=
  ∀ c < w, f ((r a).testBit c) ((r b).testBit c) = true

instance (w : ℕ) (r : ℕ → ℕ) (a b : ℕ) (f : Bool → Bool → Bool) : Decidable (All w r a b f) := by
  unfold All; infer_instance

def scanR : Prog := .while (fun _ w _ _ => w) (goR 8)

lemma scanR_spec {x B ih out} (ℓ : ℕ) (T : ℕ → Bool) (hih : ih ≤ x.length + 1) :
    ∀ n c, (∀ i < n, T (8 * (c + i) + ℓ) = true) → T (8 * (c + n) + ℓ) = false →
      8 * (c + n) + ℓ < B →
      Eval x B scanR ⟨ih, 8 * c + ℓ, T, out⟩ ⟨ih, 8 * (c + n) + ℓ, T, out⟩
  | 0, c, _, hf, _ => by
    apply Eval.while_f
    simpa [St.test] using hf
  | n + 1, c, ht, hf, hb => by
    have e1 := Eval.goR' (x := x) (B := B) (T := T) (out := out) hih 8 (8 * c + ℓ) (by omega)
    have e2 := scanR_spec (x := x) (B := B) (out := out) ℓ T hih n (c + 1)
      (fun i hi => by have := ht (i + 1) (by omega); rwa [show c + (i + 1) = c + 1 + i by ring] at this)
      (by rwa [show c + 1 + n = c + (n + 1) by ring]) (by rw [show c + 1 + n = c + (n + 1) by ring]; exact hb)
    rw [show 8 * c + ℓ + 8 = 8 * (c + 1) + ℓ by ring] at e1
    rw [show c + 1 + n = c + (n + 1) by ring] at e2
    exact Eval.while_t (by simpa [St.test] using ht 0 (by omega)) e1 e2

def clr7 : Prog := mapP 7 7 7 (fun _ _ => false)
def fin : Prog := .seq home clr7

def probe (a b : ℕ) (f : Bool → Bool → Bool) : Prog :=
  .seq (mapP a b 7 f) (.seq (goR 7) (.seq scanR (goL 7)))

def PR (x : List Bool) (B w : ℕ) (a b : ℕ) (f : Bool → Bool → Bool) (r : ℕ → ℕ) (ih : ℕ)
    (out : List Bool) (c : ℕ) (T1 : ℕ → Bool) : Prop :=
  T1 (8 * c) = decide (¬ All w r a b f) ∧
    ∃ T2, Eval x B fin ⟨ih, 8 * c, T1, out⟩ ⟨ih, 0, T2, out⟩ ∧ Enc w T2 r

lemma probe_spec {x B w ih out} (a b : ℕ) (f : Bool → Bool → Bool) (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 6) (hB : 8 * w + 8 ≤ B) (hih : ih ≤ x.length + 1) (r : ℕ → ℕ) (T : ℕ → Bool)
    (hT : Enc w T r) :
    ∃ c T1, Eval x B (probe a b f) ⟨ih, 0, T, out⟩ ⟨ih, 8 * c, T1, out⟩ ∧
      PR x B w a b f r ih out c T1 := by
  have e1 := mapP_eval (x := x) (B := B) (out := out) a b 7 f hab (by omega) (by omega) (by omega)
    hih w T hT.ruler hB
  set T1 : ℕ → Bool := fun z => if z % 8 = 7 ∧ z / 8 < w then
      f (T (8 * (z / 8) + a)) (T (8 * (z / 8) + b)) else T z with hT1
  have T1r : ∀ c, T1 (8 * c) = decide (c < w) := by
    intro c
    simp only [hT1]
    rw [if_neg (by omega)]; exact hT.ruler c
  have T17 : ∀ c, T1 (8 * c + 7) = (decide (c < w) && f ((r a).testBit c) ((r b).testBit c)) := by
    intro c
    simp only [hT1, md8 c 7 (by omega), dv8 c 7 (by omega), true_and]
    split_ifs with hc
    · rw [hT.lanes c a ha (by omega), hT.lanes c b (by omega) hb]; simp [hc]
    · rw [hT.scr c]; simp [hc]
  have hex : ∃ c, T1 (8 * c + 7) = false := ⟨w, by rw [T17]; simp⟩
  classical
  set c := Nat.find hex with hc
  have hcw : c ≤ w := Nat.find_min' hex (by rw [T17]; simp)
  have hmin : ∀ i < c, T1 (8 * (0 + i) + 7) = true := by
    intro i hi
    have := Nat.find_min hex hi
    simpa using this
  have hcf : T1 (8 * c + 7) = false := Nat.find_spec hex
  have e2 := Eval.goR' (x := x) (B := B) (T := T1) (out := out) hih 7 0 (by omega)
  have e3 := scanR_spec (x := x) (B := B) (out := out) 7 T1 hih c 0 hmin (by simpa using hcf)
    (by omega)
  have e4 := Eval.goL' (x := x) (B := B) (T := T1) (out := out) hih 7 (8 * (0 + c) + 7) (by omega)
  simp only [zero_add] at e2 e3 e4
  rw [show 8 * c + 7 - 7 = 8 * c by omega] at e4
  refine ⟨c, T1, Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4)), ?_, ?_⟩
  · rw [T1r]
    by_cases hcw' : c < w
    · have h1 := hcf
      rw [T17] at h1
      simp only [hcw', decide_true, Bool.true_and] at h1
      have : ¬ All w r a b f := fun hA => by rw [hA c hcw'] at h1; exact Bool.noConfusion h1
      simp [hcw', this]
    · have : All w r a b f := by
        intro i hi
        have := hmin i (by omega)
        rw [zero_add, T17] at this
        simpa [hi] using this
      simp [hcw', this]
  · have e5 := Eval.home' (x := x) (B := B) (T := T1) (out := out) hih (8 * c) (by omega)
    have e6 := mapP_eval (x := x) (B := B) (out := out) 7 7 7 (fun _ _ => false) le_rfl le_rfl
      (by omega) (by omega) hih w T1 T1r hB
    refine ⟨_, Eval.seq e5 e6, ?_, ?_, ?_, hT.bd⟩
    · intro c
      try dsimp only
      rw [if_neg (by omega)]; exact T1r c
    · intro c j hj1 hj6
      try dsimp only
      rw [if_neg (by omega)]
      simp only [hT1]
      rw [if_neg (by omega)]
      exact hT.lanes c j hj1 hj6
    · intro c
      try dsimp only
      simp only [md8 c 7 (by omega), dv8 c 7 (by omega), true_and]
      split_ifs with hc
      · rfl
      · rw [T17]; simp [hc]

def ifR (a b : ℕ) (f : Bool → Bool → Bool) (P Q : Prog) : Prog :=
  .seq (probe a b f) (.ite (fun _ w _ _ => w) (.seq fin Q) (.seq fin P))

lemma ifR_pos {x B w} (a b : ℕ) (f : Bool → Bool → Bool) (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 6) (hB : 8 * w + 8 ≤ B) (P Q : Prog) (r r1 : ℕ → ℕ) (hA : All w r a b f)
    (hP : RRun x B w P r r1) : RRun x B w (ifR a b f P Q) r r1 := by
  intro ih T out hih hT
  obtain ⟨c, T1, e1, h1, T2, e2, hT2⟩ := probe_spec (out := out) a b f ha hab hb hB hih r T hT
  obtain ⟨T3, e3, hT3⟩ := hP ih T2 out hih hT2
  refine ⟨T3, Eval.seq e1 (Eval.ite_f ?_ (Eval.seq e2 e3)), hT3⟩
  simp [St.test, h1, hA]

lemma ifR_neg {x B w} (a b : ℕ) (f : Bool → Bool → Bool) (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 6) (hB : 8 * w + 8 ≤ B) (P Q : Prog) (r r1 : ℕ → ℕ) (hA : ¬ All w r a b f)
    (hQ : RRun x B w Q r r1) : RRun x B w (ifR a b f P Q) r r1 := by
  intro ih T out hih hT
  obtain ⟨c, T1, e1, h1, T2, e2, hT2⟩ := probe_spec (out := out) a b f ha hab hb hB hih r T hT
  obtain ⟨T3, e3, hT3⟩ := hQ ih T2 out hih hT2
  refine ⟨T3, Eval.seq e1 (Eval.ite_t ?_ (Eval.seq e2 e3)), hT3⟩
  simp [St.test, h1, hA]

def loopW (a b : ℕ) (f : Bool → Bool → Bool) (body : Prog) : Prog :=
  .while (fun _ w _ _ => w) (.seq fin (.seq body (probe a b f)))

def whileR (a b : ℕ) (f : Bool → Bool → Bool) (body : Prog) : Prog :=
  .seq (probe a b f) (.seq (loopW a b f body) fin)

lemma loopW_spec {x B w} (a b : ℕ) (f : Bool → Bool → Bool) (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 6) (hB : 8 * w + 8 ≤ B) (body : Prog) (Inv : (ℕ → ℕ) → Prop) (μ : (ℕ → ℕ) → ℕ)
    (hstep : ∀ r, Inv r → ¬ All w r a b f → ∃ r', Inv r' ∧ μ r' < μ r ∧ RRun x B w body r r') :
    ∀ m r, μ r < m → Inv r → ∃ r', Inv r' ∧ All w r' a b f ∧
      ∀ ih out c T1, ih ≤ x.length + 1 → PR x B w a b f r ih out c T1 →
        ∃ c' T1', Eval x B (loopW a b f body) ⟨ih, 8 * c, T1, out⟩ ⟨ih, 8 * c', T1', out⟩ ∧
          PR x B w a b f r' ih out c' T1'
  | 0, r, hm, _ => absurd hm (Nat.not_lt_zero _)
  | m + 1, r, hm, hI => by
    by_cases hA : All w r a b f
    · refine ⟨r, hI, hA, fun ih out c T1 hih hP => ⟨c, T1, Eval.while_f ?_, hP⟩⟩
      simp [St.test, hP.1, hA]
    · obtain ⟨r1, hI1, hμ, hR⟩ := hstep r hI hA
      obtain ⟨r', hI', hA', hL⟩ := loopW_spec a b f ha hab hb hB body Inv μ hstep m r1 (by omega) hI1
      refine ⟨r', hI', hA', fun ih out c T1 hih hP => ?_⟩
      obtain ⟨h1, T2, e2, hT2⟩ := hP
      obtain ⟨T3, e3, hT3⟩ := hR ih T2 out hih hT2
      obtain ⟨c4, T4, e4, hP4⟩ := probe_spec (out := out) a b f ha hab hb hB hih r1 T3 hT3
      obtain ⟨c', T1', e5, hP'⟩ := hL ih out c4 T4 hih hP4
      refine ⟨c', T1', Eval.while_t ?_ (Eval.seq e2 (Eval.seq e3 e4)) e5, hP'⟩
      simp [St.test, h1, hA]

lemma whileR_spec {x B w} (a b : ℕ) (f : Bool → Bool → Bool) (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 6) (hB : 8 * w + 8 ≤ B) (body : Prog) (Inv : (ℕ → ℕ) → Prop) (μ : (ℕ → ℕ) → ℕ)
    (hstep : ∀ r, Inv r → ¬ All w r a b f → ∃ r', Inv r' ∧ μ r' < μ r ∧ RRun x B w body r r')
    (r : ℕ → ℕ) (hI : Inv r) :
    ∃ r', Inv r' ∧ All w r' a b f ∧ RRun x B w (whileR a b f body) r r' := by
  obtain ⟨r', hI', hA', hL⟩ := loopW_spec a b f ha hab hb hB body Inv μ hstep (μ r + 1) r
    (by omega) hI
  refine ⟨r', hI', hA', fun ih T out hih hT => ?_⟩
  obtain ⟨c, T1, e1, hP⟩ := probe_spec (out := out) a b f ha hab hb hB hih r T hT
  obtain ⟨c', T1', e2, hP'⟩ := hL ih out c T1 hih hP
  obtain ⟨_, T2, e3, hT2⟩ := hP'
  exact ⟨T2, Eval.seq e1 (Eval.seq e2 e3), hT2⟩

lemma all_eq {w r a b} (ha : r a < 2 ^ w) (hb : r b < 2 ^ w) :
    All w r a b (fun u v => u == v) ↔ r a = r b := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < w
    · simpa using h i hi
    · rw [testBit_ge ha (by omega), testBit_ge hb (by omega)]
  · intro h c _
    simp [h]

lemma all_zero {w r a} (ha : r a < 2 ^ w) : All w r a a (fun u _ => !u) ↔ r a = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < w
    · simpa using h i hi
    · rw [testBit_ge ha (by omega)]; simp
  · intro h c _
    simp [h]


/-! ### Layer D: trial division on registers
Registers: 1 = D, 2 = n, 3 = d, 4 = k, 5 = remainder, 6 = composite flag. -/

def eqF : Bool → Bool → Bool := fun u v => u == v
def zF : Bool → Bool → Bool := fun u _ => !u
def clrP (t : ℕ) : Prog := mapP t t t (fun _ _ => false)

lemma clr_run {x B w} (t : ℕ) (h1 : 1 ≤ t) (h6 : t ≤ 6) (hB : 8 * w + 8 ≤ B) (r : ℕ → ℕ) :
    RRun x B w (clrP t) r (Function.update r t 0) :=
  mapP_run t t t _ h1 le_rfl le_rfl h6 hB r 0 (by positivity) (fun c _ => by simp)

def Bd (N : ℕ) (r : ℕ → ℕ) : Prop := ∀ j, 1 ≤ j → j ≤ 6 → r j ≤ N

lemma Bd.lt {N w : ℕ} {r : ℕ → ℕ} (h : Bd N r) (hN : N + 1 < 2 ^ w) (j : ℕ) (h1 : 1 ≤ j)
    (h6 : j ≤ 6) : r j < 2 ^ w := by
  have := h j h1 h6; omega

lemma all_eqF {N w : ℕ} {r : ℕ → ℕ} {a b : ℕ} (h : Bd N r) (hN : N + 1 < 2 ^ w) (ha1 : 1 ≤ a)
    (ha6 : a ≤ 6) (hb1 : 1 ≤ b) (hb6 : b ≤ 6) : All w r a b eqF ↔ r a = r b :=
  all_eq (h.lt hN a ha1 ha6) (h.lt hN b hb1 hb6)

lemma all_zF {N w : ℕ} {r : ℕ → ℕ} {a : ℕ} (h : Bd N r) (hN : N + 1 < 2 ^ w) (ha1 : 1 ≤ a)
    (ha6 : a ≤ 6) : All w r a a zF ↔ r a = 0 :=
  all_zero (h.lt hN a ha1 ha6)

lemma mod_succ' (k d : ℕ) (hd : 2 ≤ d) :
    (k + 1) % d = if k % d + 1 = d then 0 else k % d + 1 := by
  have h1 := Nat.mod_add_div k d
  have h2 := Nat.mod_lt k (by omega : d > 0)
  split_ifs with h
  · have : k + 1 = d * (k / d + 1) := by
      rw [mul_add, mul_one]; generalize d * (k / d) = q at h1 ⊢; omega
    rw [this, Nat.mul_mod_right]
  · have : k + 1 = (k % d + 1) + d * (k / d) := by
      generalize d * (k / d) = q at h1 ⊢; omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

lemma Bd.upd {N : ℕ} {r : ℕ → ℕ} (h : Bd N r) (i v : ℕ) (hv : v ≤ N) :
    Bd N (Function.update r i v) := by
  intro j hj1 hj6
  by_cases hj : j = i
  · subst hj; simpa using hv
  · rw [Function.update_of_ne hj]; exact h j hj1 hj6

def modBody : Prog := .seq (incP 4) (.seq (incP 5) (ifR 3 5 eqF (clrP 5) .skip))
def modLoop : Prog := whileR 2 4 eqF modBody

lemma modLoop_spec {x B w N} (hB : 8 * w + 8 ≤ B) (hN : N + 1 < 2 ^ w) (r : ℕ → ℕ)
    (hb : Bd N r) (hd : 2 ≤ r 3) (hdn : r 3 ≤ r 2) (h4 : r 4 = 0) (h5 : r 5 = 0) :
    ∃ r', RRun x B w modLoop r r' ∧ Bd N r' ∧ r' 5 = r 2 % r 3 ∧
      ∀ j, j ≠ 4 → j ≠ 5 → r' j = r j := by
  have hN2 : r 2 ≤ N := hb 2 (by norm_num) (by norm_num)
  have hstep : ∀ s, (Bd N s ∧ s 4 ≤ r 2 ∧ s 5 = s 4 % r 3 ∧ ∀ j, j ≠ 4 → j ≠ 5 → s j = r j) →
      ¬ All w s 2 4 eqF → ∃ s', (Bd N s' ∧ s' 4 ≤ r 2 ∧ s' 5 = s' 4 % r 3 ∧
        ∀ j, j ≠ 4 → j ≠ 5 → s' j = r j) ∧ r 2 - s' 4 < r 2 - s 4 ∧
        RRun x B w modBody s s' := by
    rintro s ⟨hbs, hs4, hs5, hsj⟩ hA
    have hne : s 2 ≠ s 4 := fun h =>
      hA ((all_eqF hbs hN (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2 h)
    have h2 : s 2 = r 2 := hsj 2 (by norm_num) (by norm_num)
    have h3 : s 3 = r 3 := hsj 3 (by norm_num) (by norm_num)
    have hlt : s 4 < r 2 := by omega
    have hm := Nat.mod_lt (s 4) (show r 3 > 0 by omega)
    have hms := mod_succ' (s 4) (r 3) hd
    have e1 := inc_run (x := x) 4 (by norm_num) (by norm_num) hB s (by omega)
    have v5 : Function.update s 4 (s 4 + 1) 5 = s 5 := Function.update_of_ne (by norm_num) _ _
    have e2 := inc_run (x := x) 5 (by norm_num) (by norm_num) hB (Function.update s 4 (s 4 + 1))
      (by rw [v5]; omega)
    have hb2 := (hbs.upd 4 (s 4 + 1) (by omega)).upd 5
      (Function.update s 4 (s 4 + 1) 5 + 1) (by rw [v5]; omega)
    obtain ⟨s2, hs2⟩ : ∃ u, u = Function.update (Function.update s 4 (s 4 + 1)) 5
        (Function.update s 4 (s 4 + 1) 5 + 1) := ⟨_, rfl⟩
    rw [← hs2] at e2 hb2
    have a3 : s2 3 = r 3 := by rw [hs2]; simp [h3]
    have a4 : s2 4 = s 4 + 1 := by rw [hs2]; simp
    have a5 : s2 5 = s 5 + 1 := by rw [hs2]; simp
    have aj : ∀ j, j ≠ 4 → j ≠ 5 → s2 j = r j := by
      intro j hj4 hj5
      rw [hs2, Function.update_of_ne hj5, Function.update_of_ne hj4]; exact hsj j hj4 hj5
    by_cases hc : s 4 % r 3 + 1 = r 3
    · have hAll : All w s2 3 5 eqF :=
        (all_eqF hb2 hN (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
          (by rw [a3, a5, hs5]; omega)
      refine ⟨Function.update s2 5 0, ⟨hb2.upd 5 0 (by omega), ?_, ?_, ?_⟩, ?_,
        e1.seq (e2.seq (ifR_pos 3 5 eqF (by norm_num) (by norm_num) (by norm_num) hB _ _ _ _ hAll
          (clr_run 5 (by norm_num) (by norm_num) hB s2)))⟩
      · rw [Function.update_of_ne (by norm_num), a4]; omega
      · rw [Function.update_self, Function.update_of_ne (by norm_num), a4, hms, if_pos hc]
      · intro j hj4 hj5; rw [Function.update_of_ne hj5]; exact aj j hj4 hj5
      · rw [Function.update_of_ne (by norm_num), a4]; omega
    · have hAll : ¬ All w s2 3 5 eqF := fun h => hc (by
        have := (all_eqF hb2 hN (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1 h
        rw [a3, a5, hs5] at this; omega)
      refine ⟨s2, ⟨hb2, by rw [a4]; omega, ?_, aj⟩, by rw [a4]; omega,
        e1.seq (e2.seq (ifR_neg 3 5 eqF (by norm_num) (by norm_num) (by norm_num) hB _ _ _ _ hAll
          RRun.skip))⟩
      rw [a5, a4, hms, if_neg hc, hs5]
  obtain ⟨r', ⟨hb', h4', h5', hj'⟩, hA, hR⟩ := whileR_spec (x := x) (B := B) (w := w) 2 4 eqF
    (by norm_num) (by norm_num) (by norm_num) hB modBody
    (fun s => Bd N s ∧ s 4 ≤ r 2 ∧ s 5 = s 4 % r 3 ∧ ∀ j, j ≠ 4 → j ≠ 5 → s j = r j)
    (fun s => r 2 - s 4) hstep r ⟨hb, by omega, by rw [h4, h5, Nat.zero_mod], fun _ _ _ => rfl⟩
  refine ⟨r', hR, hb', ?_, hj'⟩
  have := (all_eqF hb' hN (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1 hA
  rw [h5', ← this, hj' 2 (by norm_num) (by norm_num)]

def setF : Prog := .seq (clrP 6) (incP 6)
def divBody : Prog :=
  .seq (clrP 4) (.seq (clrP 5) (.seq modLoop (.seq (ifR 5 5 zF setF .skip) (incP 3))))

lemma divBody_spec {x B w N} (hB : 8 * w + 8 ≤ B) (hN : N + 1 < 2 ^ w) (r : ℕ → ℕ)
    (hb : Bd N r) (hd : 2 ≤ r 3) (hdn : r 3 < r 2) :
    ∃ r', RRun x B w divBody r r' ∧ Bd N r' ∧ r' 3 = r 3 + 1 ∧
      (r' 6 = if r 2 % r 3 = 0 then 1 else r 6) ∧
      ∀ j, j ≠ 3 → j ≠ 4 → j ≠ 5 → j ≠ 6 → r' j = r j := by
  have hN2 : r 2 ≤ N := hb 2 (by norm_num) (by norm_num)
  have c1 := clr_run (x := x) 4 (by norm_num) (by norm_num) hB r
  have c2 := clr_run (x := x) 5 (by norm_num) (by norm_num) hB (Function.update r 4 0)
  have hbt : Bd N (Function.update (Function.update r 4 0) 5 0) :=
    (hb.upd 4 0 (by omega)).upd 5 0 (by omega)
  obtain ⟨r3, m1, hb3, h35, h3j⟩ := modLoop_spec (x := x) hB hN _ hbt (by simpa using hd)
    (by simp; omega) (by simp) (by simp)
  have g : ∀ j, j ≠ 4 → j ≠ 5 → r3 j = r j := by
    intro j h4 h5; rw [h3j j h4 h5]; simp [Function.update_apply, h4, h5]
  have g3 := g 3 (by norm_num) (by norm_num)
  have g6 := g 6 (by norm_num) (by norm_num)
  have h35' : r3 5 = r 2 % r 3 := by rw [h35]; simp
  by_cases hz : r 2 % r 3 = 0
  · have hAll : All w r3 5 5 zF := by
      rw [all_zF hb3 hN (by norm_num) (by norm_num), h35']; exact hz
    have s1 := clr_run (x := x) 6 (by norm_num) (by norm_num) hB r3
    have s2 := inc_run (x := x) 6 (by norm_num) (by norm_num) hB (Function.update r3 6 0)
      (by rw [Function.update_self]; omega)
    have hbs := (hb3.upd 6 0 (by omega)).upd 6 (Function.update r3 6 0 6 + 1)
      (by rw [Function.update_self]; omega)
    have f3 : Function.update (Function.update r3 6 0) 6 (Function.update r3 6 0 6 + 1) 3 = r 3 := by
      simp [g3]
    have i3 := inc_run (x := x) 3 (by norm_num) (by norm_num) hB
      (Function.update (Function.update r3 6 0) 6 (Function.update r3 6 0 6 + 1)) (by rw [f3]; omega)
    refine ⟨_, c1.seq (c2.seq (m1.seq ((ifR_pos 5 5 zF (by norm_num) (by norm_num) (by norm_num) hB
      _ _ _ _ hAll (s1.seq s2)).seq i3))), hbs.upd 3 _ (by rw [f3]; omega), ?_, ?_, ?_⟩
    · rw [Function.update_self, f3]
    · simp [hz]
    · intro j j3 j4 j5 j6; simp [Function.update_apply, j3, j6, g j j4 j5]
  · have hAll : ¬ All w r3 5 5 zF := by
      rw [all_zF hb3 hN (by norm_num) (by norm_num), h35']; exact hz
    have i3 := inc_run (x := x) 3 (by norm_num) (by norm_num) hB r3 (by rw [g3]; omega)
    refine ⟨_, c1.seq (c2.seq (m1.seq ((ifR_neg 5 5 zF (by norm_num) (by norm_num) (by norm_num) hB
      setF .skip _ _ hAll RRun.skip).seq i3))), hb3.upd 3 _ (by rw [g3]; omega), ?_, ?_, ?_⟩
    · simp [g3]
    · simp [hz, g6]
    · intro j j3 j4 j5 j6; simp [Function.update_apply, j3, g j j4 j5]

def compTest : Prog :=
  .seq (clrP 6) (.seq (clrP 3) (.seq (incP 3) (.seq (incP 3) (whileR 2 3 eqF divBody))))

lemma compTest_spec {x B w N} (hB : 8 * w + 8 ≤ B) (hN : N + 1 < 2 ^ w) (r : ℕ → ℕ)
    (hb : Bd N r) (hn : 3 ≤ r 2) :
    ∃ r', RRun x B w compTest r r' ∧ Bd N r' ∧ r' 1 = r 1 ∧ r' 2 = r 2 ∧
      (r' 6 = 0 ↔ (r 2).Prime) := by
  have hN2 : r 2 ≤ N := hb 2 (by norm_num) (by norm_num)
  have c1 := clr_run (x := x) 6 (by norm_num) (by norm_num) hB r
  have c2 := clr_run (x := x) 3 (by norm_num) (by norm_num) hB (Function.update r 6 0)
  obtain ⟨u1, hu1⟩ : ∃ u, u = Function.update (Function.update r 6 0) 3 0 := ⟨_, rfl⟩
  rw [← hu1] at c2
  have i1 := inc_run (x := x) 3 (by norm_num) (by norm_num) hB u1
    (by rw [hu1, Function.update_self]; omega)
  obtain ⟨u2, hu2⟩ : ∃ u, u = Function.update u1 3 (u1 3 + 1) := ⟨_, rfl⟩
  rw [← hu2] at i1
  have i2 := inc_run (x := x) 3 (by norm_num) (by norm_num) hB u2
    (by rw [hu2, Function.update_self, hu1, Function.update_self]; omega)
  obtain ⟨u3, hu3⟩ : ∃ u, u = Function.update u2 3 (u2 3 + 1) := ⟨_, rfl⟩
  rw [← hu3] at i2
  have u33 : u3 3 = 2 := by subst hu3 hu2 hu1; simp
  have u36 : u3 6 = 0 := by subst hu3 hu2 hu1; simp
  have u3j : ∀ j, j ≠ 3 → j ≠ 6 → u3 j = r j := by
    intro j h3 h6; subst hu3 hu2 hu1; simp [Function.update_apply, h3, h6]
  have hbu : Bd N u3 := by
    intro j hj1 hj6
    by_cases h3 : j = 3
    · subst h3; rw [u33]; omega
    · by_cases h6 : j = 6
      · subst h6; rw [u36]; omega
      · rw [u3j j h3 h6]; exact hb j hj1 hj6
  have hstep : ∀ s, (Bd N s ∧ s 1 = r 1 ∧ s 2 = r 2 ∧ 2 ≤ s 3 ∧ s 3 ≤ r 2 ∧
      (s 6 = 0 ↔ ∀ e, 2 ≤ e → e < s 3 → ¬ e ∣ r 2)) → ¬ All w s 2 3 eqF →
      ∃ s', (Bd N s' ∧ s' 1 = r 1 ∧ s' 2 = r 2 ∧ 2 ≤ s' 3 ∧ s' 3 ≤ r 2 ∧
      (s' 6 = 0 ↔ ∀ e, 2 ≤ e → e < s' 3 → ¬ e ∣ r 2)) ∧ r 2 - s' 3 < r 2 - s 3 ∧
      RRun x B w divBody s s' := by
    rintro s ⟨hbs, hs1, hs2, hs3, hs3n, hsf⟩ hA
    have hne : s 2 ≠ s 3 := fun h =>
      hA ((all_eqF hbs hN (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2 h)
    obtain ⟨r1, m1, hb1, h13, h16, h1j⟩ := divBody_spec (x := x) hB hN s hbs hs3 (by omega)
    refine ⟨r1, ⟨hb1, ?_, ?_, by omega, by omega, ?_⟩, by omega, m1⟩
    · rw [h1j 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hs1]
    · rw [h1j 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num), hs2]
    · rw [h16, h13, hs2]
      by_cases hz : r 2 % s 3 = 0
      · simp only [hz, if_true, one_ne_zero, false_iff, not_forall]
        exact ⟨s 3, hs3, by omega, not_not.2 (Nat.dvd_of_mod_eq_zero hz)⟩
      · simp only [hz, if_false, hsf]
        constructor
        · intro h e he1 he2 hd
          rcases Nat.lt_or_ge e (s 3) with h' | h'
          · exact h e he1 h' hd
          · exact hz (Nat.mod_eq_zero_of_dvd (by rwa [show e = s 3 by omega] at hd))
        · intro h e he1 he2; exact h e he1 (by omega)
  obtain ⟨r', ⟨hb', h1', h2', hd2, hdn, hf⟩, hA, hR⟩ := whileR_spec (x := x) (B := B) (w := w)
    2 3 eqF (by norm_num) (by norm_num) (by norm_num) hB divBody
    (fun s => Bd N s ∧ s 1 = r 1 ∧ s 2 = r 2 ∧ 2 ≤ s 3 ∧ s 3 ≤ r 2 ∧
      (s 6 = 0 ↔ ∀ e, 2 ≤ e → e < s 3 → ¬ e ∣ r 2))
    (fun s => r 2 - s 3) hstep u3 ⟨hbu, u3j 1 (by norm_num) (by norm_num),
      u3j 2 (by norm_num) (by norm_num), by omega, by omega,
      by rw [u36, u33]; exact ⟨fun _ e h1 h2 => absurd h2 (by omega), fun _ => rfl⟩⟩
  refine ⟨r', c1.seq (c2.seq (i1.seq (i2.seq hR))), hb', h1', h2', ?_⟩
  have := (all_eqF hb' hN (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1 hA
  rw [hf, Nat.prime_def_lt']
  constructor
  · intro h; exact ⟨by omega, fun m hm1 hm2 => h m hm1 (by omega)⟩
  · intro h e he1 he2; exact h.2 e he1 (by omega)

def initBody : Prog := .seq (incP 4) (.seq (incP 2) (incP 2))
def initN : Prog := .seq (whileR 1 4 eqF initBody) (incP 2)

def r0 (D : ℕ) : ℕ → ℕ := fun j => if j = 1 then D else 0

lemma initN_spec {x B w} (D : ℕ) (hD : 0 < D) (hB : 8 * w + 8 ≤ B) (hN : 4 * D + 1 < 2 ^ w) :
    ∃ r', RRun x B w initN (r0 D) r' ∧ Bd (4 * D) r' ∧ r' 1 = D ∧ r' 2 = 2 * D + 1 := by
  have hstep : ∀ s, (Bd (4 * D) s ∧ s 1 = D ∧ s 2 = 2 * s 4 ∧ s 4 ≤ D) → ¬ All w s 1 4 eqF →
      ∃ s', (Bd (4 * D) s' ∧ s' 1 = D ∧ s' 2 = 2 * s' 4 ∧ s' 4 ≤ D) ∧ D - s' 4 < D - s 4 ∧
      RRun x B w initBody s s' := by
    rintro s ⟨hbs, hs1, hs2, hs4⟩ hA
    have hne : s 1 ≠ s 4 := fun h =>
      hA ((all_eqF hbs hN (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2 h)
    have i1 := inc_run (x := x) 4 (by norm_num) (by norm_num) hB s (by omega)
    have v2 : Function.update s 4 (s 4 + 1) 2 = s 2 := Function.update_of_ne (by norm_num) _ _
    have i2 := inc_run (x := x) 2 (by norm_num) (by norm_num) hB (Function.update s 4 (s 4 + 1))
      (by rw [v2]; omega)
    obtain ⟨u, hu⟩ : ∃ u, u = Function.update (Function.update s 4 (s 4 + 1)) 2
        (Function.update s 4 (s 4 + 1) 2 + 1) := ⟨_, rfl⟩
    rw [← hu] at i2
    have u2 : u 2 = s 2 + 1 := by rw [hu]; simp
    have u4 : u 4 = s 4 + 1 := by rw [hu]; simp
    have u1 : u 1 = D := by rw [hu]; simp [hs1]
    have hbu : Bd (4 * D) u := by
      rw [hu]; exact (hbs.upd 4 _ (by omega)).upd 2 _ (by rw [v2]; omega)
    have i3 := inc_run (x := x) 2 (by norm_num) (by norm_num) hB u (by rw [u2]; omega)
    refine ⟨_, ⟨hbu.upd 2 _ (by rw [u2]; omega), by simp [u1], by simp [u2, u4]; omega,
      by simp [u4]; omega⟩, by simp [u4]; omega, i1.seq (i2.seq i3)⟩
  have hb0 : Bd (4 * D) (r0 D) := by
    intro j hj1 hj6
    simp only [r0]
    split_ifs <;> omega
  obtain ⟨r', ⟨hb', h1', h2', h4'⟩, hA, hR⟩ := whileR_spec (x := x) (B := B) (w := w)
    1 4 eqF (by norm_num) (by norm_num) (by norm_num) hB initBody
    (fun s => Bd (4 * D) s ∧ s 1 = D ∧ s 2 = 2 * s 4 ∧ s 4 ≤ D)
    (fun s => D - s 4) hstep (r0 D) ⟨hb0, by simp [r0], by simp [r0], by simp [r0]⟩
  have := (all_eqF hb' hN (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1 hA
  have i := inc_run (x := x) 2 (by norm_num) (by norm_num) hB r' (by omega)
  exact ⟨_, hR.seq i, hb'.upd 2 _ (by omega), by simp [h1'], by simp; omega⟩

def mainLoop : Prog := whileR 6 6 zF (.seq (incP 2) compTest)
def mainP : Prog := .seq initN (.seq compTest mainLoop)

lemma mainP_spec {x B w} (D : ℕ) (hD : 0 < D) (hB : 8 * w + 8 ≤ B) (hN : 4 * D + 1 < 2 ^ w) :
    ∃ r', RRun x B w mainP (r0 D) r' ∧ Bd (4 * D) r' ∧ LeastIntervalPrime D (r' 2) := by
  obtain ⟨p, hp, hp1, hp2⟩ := exists_prime_Ioo D hD
  obtain ⟨r1, m1, hb1, h11, h12⟩ := initN_spec (x := x) D hD hB hN
  obtain ⟨r2, m2, hb2, h21, h22, h26⟩ := compTest_spec (x := x) hB hN r1 hb1 (by omega)
  have hstep : ∀ s, (Bd (4 * D) s ∧ s 1 = D ∧ 2 * D < s 2 ∧ s 2 ≤ p ∧ (s 6 = 0 ↔ (s 2).Prime) ∧
      ∀ q, 2 * D < q → q < s 2 → ¬ q.Prime) → ¬ All w s 6 6 zF →
      ∃ s', (Bd (4 * D) s' ∧ s' 1 = D ∧ 2 * D < s' 2 ∧ s' 2 ≤ p ∧ (s' 6 = 0 ↔ (s' 2).Prime) ∧
      ∀ q, 2 * D < q → q < s' 2 → ¬ q.Prime) ∧ p - s' 2 < p - s 2 ∧
      RRun x B w (.seq (incP 2) compTest) s s' := by
    rintro s ⟨hbs, hs1, hs2a, hs2b, hs6, hsmin⟩ hA
    have hne : s 6 ≠ 0 := fun h => hA ((all_zF hbs hN (by norm_num) (by norm_num)).2 h)
    have hnp : ¬ (s 2).Prime := fun h => hne (hs6.2 h)
    have hlt : s 2 < p := by
      rcases hs2b.lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ hp) hnp
    have i1 := inc_run (x := x) 2 (by norm_num) (by norm_num) hB s (by omega)
    have hbi : Bd (4 * D) (Function.update s 2 (s 2 + 1)) := hbs.upd 2 _ (by omega)
    obtain ⟨r3, m3, hb3, h31, h32, h36⟩ := compTest_spec (x := x) hB hN _ hbi (by simp; omega)
    simp only [Function.update_self] at h32 h36
    refine ⟨r3, ⟨hb3, by rw [h31]; simp [hs1], by omega, by omega, by rw [h36, h32], ?_⟩,
      by omega, i1.seq m3⟩
    intro q hq1 hq2
    rcases Nat.lt_or_ge q (s 2) with h | h
    · exact hsmin q hq1 h
    · rw [show q = s 2 by omega]; exact hnp
  obtain ⟨r', ⟨hb', h1', h2a, h2b, h6', hmin⟩, hA, hR⟩ := whileR_spec (x := x) (B := B) (w := w)
    6 6 zF (by norm_num) (by norm_num) (by norm_num) hB (.seq (incP 2) compTest)
    (fun s => Bd (4 * D) s ∧ s 1 = D ∧ 2 * D < s 2 ∧ s 2 ≤ p ∧ (s 6 = 0 ↔ (s 2).Prime) ∧
      ∀ q, 2 * D < q → q < s 2 → ¬ q.Prime)
    (fun s => p - s 2) hstep r2 ⟨hb2, by rw [h21, h11], by omega, by omega, by rw [h26, h22],
      fun q h1 h2 => by omega⟩
  refine ⟨r', m1.seq (m2.seq hR), hb', ?_⟩
  have h0 := (all_zF hb' hN (by norm_num) (by norm_num)).1 hA
  have hpr := h6'.1 h0
  refine ⟨hpr, h2a, by omega, fun q hq hq1 hq2 => ?_⟩
  by_contra hc
  exact hmin q hq1 (by omega) hq

/-! ### Layer E: printing `natCode` of register 2 -/

def emitP (b : Bool) : Prog := .act none .stay .stay (some b)

lemma Eval.emit' {x B ih wh T out} (b : Bool) (hih : ih ≤ x.length + 1) (hb : wh < B) :
    Eval x B (emitP b) ⟨ih, wh, T, out⟩ ⟨ih, wh, T, out ++ [b]⟩ := by
  unfold emitP
  have := @Eval.act x B none .stay .stay (some b) ⟨ih, wh, T, out⟩
    (by simpa [St.act, Move.apply] using hih) (by simpa [St.act, Move.apply] using hb)
  simpa [St.act, Move.apply, Function.update_eq_self] using this

def scanL : Prog := .while (fun _ w _ _ => !w) (goL 8)

lemma scanL_spec {x B ih out} (ℓ : ℕ) (T : ℕ → Bool) (hih : ih ≤ x.length + 1) :
    ∀ n t, (∀ i, 0 < i → i ≤ n → T (8 * (t + i) + ℓ) = false) → T (8 * t + ℓ) = true →
      8 * (t + n) + ℓ < B →
      Eval x B scanL ⟨ih, 8 * (t + n) + ℓ, T, out⟩ ⟨ih, 8 * t + ℓ, T, out⟩
  | 0, t, _, ht, _ => by
    apply Eval.while_f; simp [St.test, ht]
  | n + 1, t, hf, ht, hb => by
    have e1 := Eval.goL' (x := x) (B := B) (T := T) (out := out) hih 8 (8 * (t + (n + 1)) + ℓ) hb
    rw [show 8 * (t + (n + 1)) + ℓ - 8 = 8 * (t + n) + ℓ by omega] at e1
    have e2 := scanL_spec (x := x) (B := B) (out := out) ℓ T hih n t
      (fun i h1 h2 => hf i h1 (by omega)) ht (by omega)
    exact Eval.while_t (by simp [St.test, hf (n + 1) (by omega) le_rfl]) e1 e2

def markCol : Prog := .seq (goR 7) (.seq (.act (some true) .stay .stay none) (goL 7))

lemma markCol_spec {x B ih out} (T : ℕ → Bool) (hih : ih ≤ x.length + 1) (c : ℕ)
    (hb : 8 * c + 7 < B) :
    Eval x B markCol ⟨ih, 8 * c, T, out⟩ ⟨ih, 8 * c, Function.update T (8 * c + 7) true, out⟩ := by
  have e1 := Eval.goR' (x := x) (B := B) (T := T) (out := out) hih 7 (8 * c) hb
  have e2 := Eval.wrR (x := x) (B := B) (T := T) (out := out) (wh := 8 * c + 7) true .stay hih
    (by simpa [Move.apply] using hb)
  have e3 := Eval.goL' (x := x) (B := B) (T := Function.update T (8 * c + 7) true) (out := out)
    hih 7 (8 * c + 7) hb
  simp only [Move.apply] at e2
  rw [show 8 * c + 7 - 7 = 8 * c by omega] at e3
  exact Eval.seq e1 (Eval.seq e2 e3)

def markRest : Prog := .while (fun _ _ _ we => !we) (.seq (goL 8) markCol)

lemma markRest_spec {x B ih out} (hih : ih ≤ x.length + 1) :
    ∀ (t : ℕ) (T : ℕ → Bool), 8 * t + 8 ≤ B →
      Eval x B markRest ⟨ih, 8 * t, T, out⟩
        ⟨ih, 0, fun z => if z % 8 = 7 ∧ z / 8 < t then true else T z, out⟩
  | 0, T, _ => by
    have : (fun z => if z % 8 = 7 ∧ z / 8 < 0 then true else T z) = T := by
      funext z; rw [if_neg (by omega)]
    rw [this]
    apply Eval.while_f; simp [St.test]
  | t + 1, T, hb => by
    have e1 := Eval.goL' (x := x) (B := B) (T := T) (out := out) hih 8 (8 * (t + 1)) (by omega)
    rw [show 8 * (t + 1) - 8 = 8 * t by omega] at e1
    have e2 := markCol_spec (x := x) (B := B) (out := out) T hih t (by omega)
    have e3 := markRest_spec (x := x) (B := B) (out := out) hih t
      (Function.update T (8 * t + 7) true) (by omega)
    have e : (fun z => if z % 8 = 7 ∧ z / 8 < t then true else Function.update T (8 * t + 7) true z)
        = (fun z => if z % 8 = 7 ∧ z / 8 < t + 1 then true else T z) := by
      funext z
      by_cases hz : z = 8 * t + 7
      · subst hz; simp; left; omega
      · rw [Function.update_of_ne hz]
        by_cases h : z % 8 = 7 ∧ z / 8 < t
        · rw [if_pos h, if_pos ⟨h.1, by omega⟩]
        · rw [if_neg h, if_neg (by omega)]
    rw [e] at e3
    exact Eval.while_t (by simp [St.test]) (Eval.seq e1 e2) e3

def markP : Prog := .seq scanR (.seq (goR 3) (.seq scanL (.seq (goL 3) (.seq markCol markRest))))

lemma markP_spec {x B ih out} (hih : ih ≤ x.length + 1) (w : ℕ) (hB : 8 * w + 8 ≤ B)
    (T : ℕ → Bool) (m : ℕ) (hm0 : m ≠ 0) (hmw : m < 2 ^ w)
    (hr : ∀ c, T (8 * c) = decide (c < w)) (h3 : ∀ c, T (8 * c + 3) = m.testBit c) :
    Eval x B markP ⟨ih, 0, T, out⟩
      ⟨ih, 0, fun z => if z % 8 = 7 ∧ z / 8 ≤ Nat.log 2 m then true else T z, out⟩ := by
  set t := Nat.log 2 m with ht
  have htw : t < w := Nat.log_lt_of_lt_pow hm0 hmw
  have hmt : m < 2 ^ (t + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hbit : m.testBit t = true := by
    have := Nat.testBit_log2 hm0
    rwa [Nat.log2_eq_log_two] at this
  have e1 := scanR_spec (x := x) (B := B) (out := out) 0 T hih w 0
    (fun i hi => by rw [add_zero, hr]; simp; omega) (by rw [add_zero, hr]; simp) (by omega)
  simp only [zero_add, mul_zero, add_zero] at e1
  have e2 := Eval.goR' (x := x) (B := B) (T := T) (out := out) hih 3 (8 * w) (by omega)
  have e3 := scanL_spec (x := x) (B := B) (out := out) 3 T hih (w - t) t
    (fun i h1 h2 => by rw [h3]; exact testBit_ge hmt (by omega)) (by rw [h3]; exact hbit)
    (by omega)
  rw [show 8 * (t + (w - t)) + 3 = 8 * w + 3 by omega] at e3
  have e4 := Eval.goL' (x := x) (B := B) (T := T) (out := out) hih 3 (8 * t + 3) (by omega)
  rw [show 8 * t + 3 - 3 = 8 * t by omega] at e4
  have e5 := markCol_spec (x := x) (B := B) (out := out) T hih t (by omega)
  have e6 := markRest_spec (x := x) (B := B) (out := out) hih t
    (Function.update T (8 * t + 7) true) (by omega)
  have e : (fun z => if z % 8 = 7 ∧ z / 8 < t then true else Function.update T (8 * t + 7) true z)
      = (fun z => if z % 8 = 7 ∧ z / 8 ≤ t then true else T z) := by
    funext z
    by_cases hz : z = 8 * t + 7
    · subst hz; simp; left; omega
    · rw [Function.update_of_ne hz]
      by_cases h : z % 8 = 7 ∧ z / 8 < t
      · rw [if_pos h, if_pos ⟨h.1, by omega⟩]
      · rw [if_neg h, if_neg (by omega)]
  rw [e] at e6
  exact Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 e6))))

def onesL : Prog := .while (fun _ w _ _ => w) (.seq (emitP true) (goR 8))

lemma onesL_spec {x B ih} (T : ℕ → Bool) (hih : ih ≤ x.length + 1) :
    ∀ n c out, (∀ i < n, T (8 * (c + i) + 7) = true) → T (8 * (c + n) + 7) = false →
      8 * (c + n) + 7 < B →
      Eval x B onesL ⟨ih, 8 * c + 7, T, out⟩ ⟨ih, 8 * (c + n) + 7, T, out ++ List.replicate n true⟩
  | 0, c, out, _, hf, _ => by
    simp only [List.replicate_zero, List.append_nil]
    apply Eval.while_f; simpa [St.test] using hf
  | n + 1, c, out, ht, hf, hb => by
    have e1 := Eval.emit' (x := x) (B := B) (T := T) (out := out) (wh := 8 * c + 7) true hih
      (by omega)
    have e2 := Eval.goR' (x := x) (B := B) (T := T) (out := out ++ [true]) hih 8 (8 * c + 7)
      (by omega)
    rw [show 8 * c + 7 + 8 = 8 * (c + 1) + 7 by ring] at e2
    have e3 := onesL_spec (x := x) (B := B) T hih n (c + 1) (out ++ [true])
      (fun i hi => by have := ht (i + 1) (by omega); rwa [show c + (i + 1) = c + 1 + i by ring] at this)
      (by rwa [show c + 1 + n = c + (n + 1) by ring]) (by rw [show c + 1 + n = c + (n + 1) by ring]; exact hb)
    rw [show c + 1 + n = c + (n + 1) by ring, List.append_assoc, List.singleton_append,
      ← List.replicate_succ] at e3
    exact Eval.while_t (by simpa [St.test] using ht 0 (by omega)) (Eval.seq e1 e2) e3

def bitsL : Prog :=
  .while (fun _ w _ _ => w) (.seq (goL 5) (.seq (rd fun u => emitP u) (.seq (goR 5) (goR 8))))

lemma bitsL_spec {x B ih} (T : ℕ → Bool) (hih : ih ≤ x.length + 1) :
    ∀ n c out, (∀ i < n, T (8 * (c + i) + 7) = true) → T (8 * (c + n) + 7) = false →
      8 * (c + n) + 7 < B →
      Eval x B bitsL ⟨ih, 8 * c + 7, T, out⟩
        ⟨ih, 8 * (c + n) + 7, T, out ++ (List.range n).map (fun i => T (8 * (c + i) + 2))⟩
  | 0, c, out, _, hf, _ => by
    simp only [List.range_zero, List.map_nil, List.append_nil]
    apply Eval.while_f; simpa [St.test] using hf
  | n + 1, c, out, ht, hf, hb => by
    have e1 := Eval.goL' (x := x) (B := B) (T := T) (out := out) hih 5 (8 * c + 7) (by omega)
    rw [show 8 * c + 7 - 5 = 8 * c + 2 by omega] at e1
    have e2 : Eval x B (rd fun u => emitP u) ⟨ih, 8 * c + 2, T, out⟩
        ⟨ih, 8 * c + 2, T, out ++ [T (8 * c + 2)]⟩ :=
      Eval.rd' _ (Eval.emit' (x := x) (B := B) _ hih (by omega))
    have e3 := Eval.goR' (x := x) (B := B) (T := T) (out := out ++ [T (8 * c + 2)]) hih 5
      (8 * c + 2) (by omega)
    have e4 := Eval.goR' (x := x) (B := B) (T := T) (out := out ++ [T (8 * c + 2)]) hih 8
      (8 * c + 2 + 5) (by omega)
    rw [show 8 * c + 2 + 5 + 8 = 8 * (c + 1) + 7 by ring] at e4
    have e5 := bitsL_spec (x := x) (B := B) T hih n (c + 1) (out ++ [T (8 * c + 2)])
      (fun i hi => by have := ht (i + 1) (by omega); rwa [show c + (i + 1) = c + 1 + i by ring] at this)
      (by rwa [show c + 1 + n = c + (n + 1) by ring]) (by rw [show c + 1 + n = c + (n + 1) by ring]; exact hb)
    have hl : out ++ [T (8 * c + 2)] ++ (List.range n).map (fun i => T (8 * (c + 1 + i) + 2)) =
        out ++ (List.range (n + 1)).map (fun i => T (8 * (c + i) + 2)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.append_assoc,
        List.singleton_append]
      congr 2
      apply List.map_congr_left
      intro i _
      simp only [Function.comp, Nat.succ_eq_add_one]
      ring_nf
    rw [show c + 1 + n = c + (n + 1) by ring, hl] at e5
    exact Eval.while_t (by simpa [St.test] using ht 0 (by omega))
      (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))) e5

def printP : Prog :=
  .seq (.seq (mapP 2 2 3 (fun u _ => u)) (incP 3)) (.seq markP (.seq (goR 7) (.seq onesL
    (.seq (emitP false) (.seq home (.seq (goR 7) bitsL))))))

lemma print_spec {x B w ih out} (hih : ih ≤ x.length + 1) (hB : 8 * w + 8 ≤ B) (r : ℕ → ℕ)
    (T : ℕ → Bool) (hT : Enc w T r) (hp : r 2 + 1 < 2 ^ w) :
    ∃ s', Eval x B printP ⟨ih, 0, T, out⟩ s' ∧ s'.out = out ++ natCode (r 2) := by
  have m1 := mapP_run (x := x) 2 2 3 (fun u _ => u) (by norm_num) le_rfl (by norm_num) (by norm_num)
    hB r (r 2) (by omega) (fun c _ => rfl)
  have i1 := inc_run (x := x) 3 (by norm_num) (by norm_num) hB (Function.update r 3 (r 2))
    (by simp; omega)
  obtain ⟨T2, e12, hT2⟩ := (m1.seq i1) ih T out hih hT
  have q3 : Function.update (Function.update r 3 (r 2)) 3 (Function.update r 3 (r 2) 3 + 1) 3
      = r 2 + 1 := by simp
  have q2 : Function.update (Function.update r 3 (r 2)) 3 (Function.update r 3 (r 2) 3 + 1) 2
      = r 2 := by simp
  set t := Nat.log 2 (r 2 + 1) with ht
  have htw : t < w := Nat.log_lt_of_lt_pow (by omega) hp
  have e3 := markP_spec (x := x) (B := B) (out := out) hih w hB T2 (r 2 + 1) (by omega) hp
    hT2.ruler (fun c => by rw [hT2.lanes c 3 (by norm_num) (by norm_num), q3])
  rw [← ht] at e3
  set T3 : ℕ → Bool := fun z => if z % 8 = 7 ∧ z / 8 ≤ t then true else T2 z with hT3
  have T37 : ∀ c, T3 (8 * c + 7) = decide (c ≤ t) := by
    intro c
    simp only [hT3, md8 c 7 (by omega), dv8 c 7 (by omega), true_and]
    split_ifs with h
    · simp [h]
    · rw [hT2.scr c]; simp [h]
  have T32 : ∀ c, T3 (8 * c + 2) = (r 2).testBit c := by
    intro c
    simp only [hT3, md8 c 2 (by omega)]
    rw [if_neg (by omega), hT2.lanes c 2 (by norm_num) (by norm_num), q2]
  have e4 := Eval.goR' (x := x) (B := B) (T := T3) (out := out) hih 7 0 (by omega)
  have e5 := onesL_spec (x := x) (B := B) T3 hih (t + 1) 0 out
    (fun i hi => by rw [T37]; simp; omega) (by rw [T37]; simp) (by omega)
  simp only [zero_add] at e4 e5
  have e6 := Eval.emit' (x := x) (B := B) (T := T3) (out := out ++ List.replicate (t + 1) true)
    (wh := 8 * (t + 1) + 7) false hih (by omega)
  have e7 := Eval.home' (x := x) (B := B) (T := T3)
    (out := out ++ List.replicate (t + 1) true ++ [false]) hih (8 * (t + 1) + 7) (by omega)
  have e8 := Eval.goR' (x := x) (B := B) (T := T3)
    (out := out ++ List.replicate (t + 1) true ++ [false]) hih 7 0 (by omega)
  have e9 := bitsL_spec (x := x) (B := B) T3 hih (t + 1) 0
    (out ++ List.replicate (t + 1) true ++ [false])
    (fun i hi => by rw [T37]; simp; omega) (by rw [T37]; simp) (by omega)
  simp only [zero_add] at e8 e9
  refine ⟨_, Eval.seq e12 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6 (Eval.seq e7
    (Eval.seq e8 e9)))))), ?_⟩
  simp only [natCode, bits, List.append_assoc]
  rw [← ht]
  congr 3
  apply List.map_congr_left
  intro i _
  exact T32 i
/-! ### Layer F: reading `natCode D` from the input tape -/

def mvI : Prog := .act none .stay .right none
def wrT : Prog := .act (some true) .stay .stay none

lemma Eval.mvI' {x B ih wh T out} (hih : ih + 1 ≤ x.length + 1) (hb : wh < B) :
    Eval x B mvI ⟨ih, wh, T, out⟩ ⟨ih + 1, wh, T, out⟩ := by
  unfold mvI
  have := @Eval.act x B none .stay .right none ⟨ih, wh, T, out⟩
    (by simpa [St.act, Move.apply] using hih) (by simpa [St.act, Move.apply] using hb)
  simpa [St.act, Move.apply, Function.update_eq_self] using this

lemma Eval.wrT' {x B ih wh T out} (hih : ih ≤ x.length + 1) (hb : wh < B) :
    Eval x B wrT ⟨ih, wh, T, out⟩ ⟨ih, wh, Function.update T wh true, out⟩ := by
  have := Eval.wrR (x := x) (B := B) (T := T) (out := out) (wh := wh) true .stay hih
    (by simpa [Move.apply] using hb)
  unfold wrT
  simpa [Move.apply] using this

def uLoop : Prog := .while (fun a _ _ _ => a == some true) (.seq wrT (.seq (goR 8) mvI))

lemma uLoop_spec {x B out} :
    ∀ n c (T : ℕ → Bool), (∀ i < n, x[c + i]? = some true) → x[c + n]? = some false →
      8 * (c + n) < B → c + n + 1 ≤ x.length + 1 →
      Eval x B uLoop ⟨c + 1, 8 * c, T, out⟩
        ⟨c + n + 1, 8 * (c + n), fun z => if z % 8 = 0 ∧ c ≤ z / 8 ∧ z / 8 < c + n then true
          else T z, out⟩
  | 0, c, T, _, hf, _, _ => by
    have : (fun z => if z % 8 = 0 ∧ c ≤ z / 8 ∧ z / 8 < c + 0 then true else T z) = T := by
      funext z; rw [if_neg (by omega)]
    rw [this]
    have hf' : x[c]? = some false := by simpa using hf
    apply Eval.while_f
    simp [St.test, hf']
  | n + 1, c, T, ht, hf, hb, hl => by
    have h0 : x[c]? = some true := by simpa using ht 0 (by omega)
    have e1 := Eval.wrT' (x := x) (B := B) (T := T) (out := out) (ih := c + 1) (wh := 8 * c)
      (by omega) (by omega)
    have e2 := Eval.goR' (x := x) (B := B) (T := Function.update T (8 * c) true) (out := out)
      (ih := c + 1) (by omega) 8 (8 * c) (by omega)
    have e3 := Eval.mvI' (x := x) (B := B) (T := Function.update T (8 * c) true) (out := out)
      (ih := c + 1) (wh := 8 * c + 8) (by omega) (by omega)
    rw [show 8 * c + 8 = 8 * (c + 1) by ring] at e2 e3
    have e4 := uLoop_spec (x := x) (B := B) (out := out) n (c + 1) (Function.update T (8 * c) true)
      (fun i hi => by rw [show c + 1 + i = c + (i + 1) by ring]; exact ht (i + 1) (by omega))
      (by rwa [show c + 1 + n = c + (n + 1) by ring])
      (by rw [show c + 1 + n = c + (n + 1) by ring]; exact hb)
      (by omega)
    have e : (fun z => if z % 8 = 0 ∧ c + 1 ≤ z / 8 ∧ z / 8 < c + 1 + n then true
        else Function.update T (8 * c) true z) =
        (fun z => if z % 8 = 0 ∧ c ≤ z / 8 ∧ z / 8 < c + (n + 1) then true else T z) := by
      funext z
      by_cases hz : z = 8 * c
      · subst hz; simp
      · rw [Function.update_of_ne hz]
        by_cases h : z % 8 = 0 ∧ c + 1 ≤ z / 8 ∧ z / 8 < c + 1 + n
        · rw [if_pos h, if_pos ⟨h.1, by omega, by omega⟩]
        · rw [if_neg h, if_neg (by omega)]
    rw [e, show c + 1 + n + 1 = c + (n + 1) + 1 by ring, show c + 1 + n = c + (n + 1) by ring]
      at e4
    exact Eval.while_t (by simp [St.test, h0]) (Eval.seq e1 (Eval.seq e2 e3)) e4

def bLoop : Prog :=
  .while (fun a _ _ _ => a != none)
    (.seq (.ite (fun a _ _ _ => a == some true) wrT .skip) (.seq (goR 8) mvI))

lemma bLoop_spec {x B out} (f : ℕ → Bool) :
    ∀ n c j (T : ℕ → Bool), (∀ i < n, x[j + i]? = some (f (c + i))) → x[j + n]? = none →
      8 * (c + n) + 1 < B → j + n + 1 ≤ x.length + 1 →
      Eval x B bLoop ⟨j + 1, 8 * c + 1, T, out⟩
        ⟨j + n + 1, 8 * (c + n) + 1, fun z => if z % 8 = 1 ∧ c ≤ z / 8 ∧ z / 8 < c + n ∧
          f (z / 8) = true then true else T z, out⟩
  | 0, c, j, T, _, hf, _, _ => by
    have : (fun z => if z % 8 = 1 ∧ c ≤ z / 8 ∧ z / 8 < c + 0 ∧ f (z / 8) = true then true
        else T z) = T := by
      funext z; rw [if_neg (by omega)]
    rw [this]
    have hf' : x[j]? = none := by simpa using hf
    apply Eval.while_f
    simp [St.test, hf']
  | n + 1, c, j, T, ht, hf, hb, hl => by
    have h0 : x[j]? = some (f c) := by simpa using ht 0 (by omega)
    set T' : ℕ → Bool := fun z => if z = 8 * c + 1 ∧ f c = true then true else T z with hT'
    have e1 : Eval x B (.ite (fun a _ _ _ => a == some true) wrT .skip)
        ⟨j + 1, 8 * c + 1, T, out⟩ ⟨j + 1, 8 * c + 1, T', out⟩ := by
      have hx := ht 0 (by omega)
      simp only [add_zero] at hx
      cases hfc : f c
      · have : T' = T := by funext z; simp [hT', hfc]
        rw [this]
        exact Eval.ite_f (by simp [St.test, hx, hfc]) Eval.skip
      · have : T' = Function.update T (8 * c + 1) true := by
          funext z; simp only [hT', hfc, and_true, Function.update_apply]
        rw [this]
        exact Eval.ite_t (by simp [St.test, hx, hfc]) (Eval.wrT' (by omega) (by omega))
    have e2 := Eval.goR' (x := x) (B := B) (T := T') (out := out) (ih := j + 1) (by omega) 8
      (8 * c + 1) (by omega)
    have e3 := Eval.mvI' (x := x) (B := B) (T := T') (out := out) (ih := j + 1)
      (wh := 8 * c + 1 + 8) (by omega) (by omega)
    rw [show 8 * c + 1 + 8 = 8 * (c + 1) + 1 by ring] at e2 e3
    have e4 := bLoop_spec (x := x) (B := B) (out := out) f n (c + 1) (j + 1) T'
      (fun i hi => by
        rw [show j + 1 + i = j + (i + 1) by ring, show c + 1 + i = c + (i + 1) by ring]
        exact ht (i + 1) (by omega))
      (by rwa [show j + 1 + n = j + (n + 1) by ring])
      (by rw [show c + 1 + n = c + (n + 1) by ring]; exact hb)
      (by omega)
    have e : (fun z => if z % 8 = 1 ∧ c + 1 ≤ z / 8 ∧ z / 8 < c + 1 + n ∧ f (z / 8) = true then true
        else T' z) =
        (fun z => if z % 8 = 1 ∧ c ≤ z / 8 ∧ z / 8 < c + (n + 1) ∧ f (z / 8) = true then true
          else T z) := by
      funext z
      by_cases hz : z = 8 * c + 1
      · subst hz
        have h1 : (8 * c + 1) % 8 = 1 := by omega
        have h2 : (8 * c + 1) / 8 = c := by omega
        simp [hT', h1, h2]
      · have hT'z : T' z = T z := by simp [hT', hz]
        rw [hT'z]
        by_cases h : z % 8 = 1 ∧ c + 1 ≤ z / 8 ∧ z / 8 < c + 1 + n ∧ f (z / 8) = true
        · rw [if_pos h, if_pos ⟨h.1, by omega, by omega, h.2.2.2⟩]
        · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, by omega, by omega, h'.2.2.2⟩)]
    rw [e, show j + 1 + n + 1 = j + (n + 1) + 1 by ring, show c + 1 + n = c + (n + 1) by ring]
      at e4
    exact Eval.while_t (by simp [St.test, h0]) (Eval.seq e1 (Eval.seq e2 e3)) e4

def initP : Prog :=
  .seq mvI (.seq uLoop (.seq (.seq wrT (goR 8)) (.seq (.seq wrT (goR 8)) (.seq wrT
    (.seq home (.seq mvI (.seq (goR 1) (.seq bLoop home))))))))

lemma code_facts (b D : ℕ) :
    let x := List.replicate b true ++ [false] ++ (List.range b).map D.testBit
    x.length = 2 * b + 1 ∧ (∀ i < b, x[i]? = some true) ∧ x[b]? = some false ∧
      (∀ i < b, x[b + 1 + i]? = some (D.testBit i)) ∧ x[2 * b + 1]? = none := by
  intro x
  refine ⟨by simp [x]; omega, fun i hi => ?_, ?_, fun i hi => ?_, ?_⟩
  · simp only [x, List.append_assoc]
    rw [List.getElem?_append_left (by simpa using hi)]
    simp [hi]
  · simp only [x, List.append_assoc]
    rw [List.getElem?_append_right (by simp)]
    simp
  · simp only [x, List.append_assoc]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate, List.singleton_append]
    rw [show b + 1 + i - b = i + 1 by omega]
    simp [hi]
  · rw [List.getElem?_eq_none]; simp [x]; omega

lemma init_spec (D : ℕ) (hD : 0 < D) (B : ℕ) (hB : 8 * (Nat.log 2 (D + 1) + 4) + 8 ≤ B) :
    ∃ ih T, ih ≤ (natCode D).length + 1 ∧
      Eval (natCode D) B initP ⟨0, 0, fun _ => false, []⟩ ⟨ih, 0, T, []⟩ ∧
      Enc (Nat.log 2 (D + 1) + 4) T (r0 D) := by
  set b := Nat.log 2 (D + 1) + 1 with hbdef
  have hx : natCode D = List.replicate b true ++ [false] ++ (List.range b).map D.testBit := rfl
  obtain ⟨hlen, hx1, hx2, hx3, hx4⟩ := code_facts b D
  rw [← hx] at hlen hx1 hx2 hx3 hx4
  have hw : Nat.log 2 (D + 1) + 4 = b + 3 := by omega
  rw [hw] at hB ⊢
  have hDb : D < 2 ^ b := by
    have : D + 1 < 2 ^ b := by rw [hbdef]; exact Nat.lt_pow_succ_log_self (by norm_num) _
    omega
  set x := natCode D
  have e0 := Eval.mvI' (x := x) (B := B) (T := fun _ => false) (out := []) (ih := 0) (wh := 0)
    (by omega) (by omega)
  have e1 := uLoop_spec (x := x) (B := B) (out := []) b 0 (fun _ => false)
    (fun i hi => by rw [zero_add]; exact hx1 i hi) (by rw [zero_add]; exact hx2) (by omega)
    (by omega)
  simp only [zero_add, mul_zero, Nat.zero_le, true_and] at e1
  set TA : ℕ → Bool := fun z => if z % 8 = 0 ∧ z / 8 < b then true else false with hTA
  have e2 := Eval.wrT' (x := x) (B := B) (T := TA) (out := []) (ih := b + 1) (wh := 8 * b)
    (by omega) (by omega)
  have e3 := Eval.goR' (x := x) (B := B) (T := Function.update TA (8 * b) true) (out := [])
    (ih := b + 1) (by omega) 8 (8 * b) (by omega)
  set TB1 := Function.update TA (8 * b) true
  have e4 := Eval.wrT' (x := x) (B := B) (T := TB1) (out := []) (ih := b + 1) (wh := 8 * b + 8)
    (by omega) (by omega)
  have e5 := Eval.goR' (x := x) (B := B) (T := Function.update TB1 (8 * b + 8) true) (out := [])
    (ih := b + 1) (by omega) 8 (8 * b + 8) (by omega)
  set TB2 := Function.update TB1 (8 * b + 8) true
  have e6 := Eval.wrT' (x := x) (B := B) (T := TB2) (out := []) (ih := b + 1)
    (wh := 8 * b + 8 + 8) (by omega) (by omega)
  set TB := Function.update TB2 (8 * b + 8 + 8) true with hTB
  have e7 := Eval.home' (x := x) (B := B) (T := TB) (out := []) (ih := b + 1) (by omega)
    (8 * b + 8 + 8) (by omega)
  have e8 := Eval.mvI' (x := x) (B := B) (T := TB) (out := []) (ih := b + 1) (wh := 0)
    (by omega) (by omega)
  have e9 := Eval.goR' (x := x) (B := B) (T := TB) (out := []) (ih := b + 1 + 1) (by omega) 1 0
    (by omega)
  have e10 := bLoop_spec (x := x) (B := B) (out := []) D.testBit b 0 (b + 1) TB
    (fun i hi => by rw [zero_add]; exact hx3 i hi) (by rw [show b + 1 + b = 2 * b + 1 by ring]; exact hx4)
    (by omega) (by omega)
  simp only [zero_add, mul_zero, Nat.zero_le, true_and] at e9 e10
  set TC : ℕ → Bool := fun z => if z % 8 = 1 ∧ z / 8 < b ∧ D.testBit (z / 8) = true then true
    else TB z with hTC
  have e11 := Eval.home' (x := x) (B := B) (T := TC) (out := []) (ih := b + 1 + b + 1) (by omega)
    (8 * b + 1) (by omega)
  refine ⟨b + 1 + b + 1, TC, by omega, Eval.seq e0 (Eval.seq e1 (Eval.seq (Eval.seq e2 e3)
    (Eval.seq (Eval.seq e4 e5) (Eval.seq e6 (Eval.seq e7 (Eval.seq e8 (Eval.seq e9
    (Eval.seq e10 e11)))))))), ?_⟩
  -- the tape TB differs from TA only on the ruler lane
  have TBnz : ∀ z, z % 8 ≠ 0 → TB z = false := by
    intro z hz
    simp only [hTB, TB2, TB1, Function.update_apply]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), hTA]
    simp only [ite_eq_right_iff]; omega
  constructor
  · intro c
    simp only [hTC]
    rw [if_neg (by omega)]
    simp only [hTB, TB2, TB1, Function.update_apply, hTA]
    by_cases h1 : c < b
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      simp; omega
    · by_cases h2 : c = b
      · subst h2; simp
      · by_cases h3 : c = b + 1
        · rw [if_neg (by omega), if_pos (by omega)]; simp; omega
        · by_cases h4 : c = b + 2
          · rw [if_pos (by omega)]; simp; omega
          · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            simp; omega
  · intro c j hj1 hj6
    simp only [hTC, md8 c j (by omega), dv8 c j (by omega)]
    by_cases hj : j = 1
    · subst hj
      simp only [r0, if_true, true_and]
      rw [TBnz _ (by omega)]
      by_cases hc : c < b
      · simp [hc]
      · simp only [hc, false_and, if_false]
        exact (testBit_ge hDb (by omega)).symm
    · rw [if_neg (by omega), TBnz _ (by omega)]
      simp [r0, hj]
  · intro c
    simp only [hTC, md8 c 7 (by omega)]
    rw [if_neg (by omega), TBnz _ (by omega)]
  · intro j hj1 hj6
    simp only [r0]
    split_ifs
    · exact lt_of_lt_of_le hDb (Nat.pow_le_pow_right (by norm_num) (by omega))
    · positivity
/-! ### Assembly -/

/-- A structured program computing the least prime in `(2D,4D)`
within `K*(log₂(D+1)+1)` work cells, printing `natCode p`. -/
theorem alg_exists : ∃ (P : Prog) (K : ℕ), 0 < K ∧ ∀ D : ℕ, 0 < D → ∃ p : ℕ,
    LeastIntervalPrime D p ∧ ∃ s' : St,
      Eval (natCode D) (K * (Nat.log 2 (D + 1) + 1)) P ⟨0, 0, fun _ => false, []⟩ s' ∧
      s'.out = natCode p := by
  refine ⟨.seq initP (.seq mainP printP), 40, by norm_num, fun D hD => ?_⟩
  have hB : 8 * (Nat.log 2 (D + 1) + 4) + 8 ≤ 40 * (Nat.log 2 (D + 1) + 1) := by omega
  have hN : 4 * D + 1 < 2 ^ (Nat.log 2 (D + 1) + 4) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (D + 1)
    rw [Nat.succ_eq_add_one, pow_succ] at this
    rw [pow_add]; norm_num; omega
  obtain ⟨ih, T, hih, e1, hT⟩ := init_spec D hD _ hB
  obtain ⟨r', m, hb', hlp⟩ := mainP_spec (x := natCode D) D hD hB hN
  obtain ⟨T', e2, hT'⟩ := m ih T [] hih hT
  obtain ⟨s', e3, ho⟩ := print_spec (x := natCode D) (out := []) hih hB r' T' hT'
    (by have := hb' 2 (by norm_num) (by norm_num); omega)
  exact ⟨r' 2, hlp, s', Eval.seq e1 (Eval.seq e2 e3), by simpa using ho⟩

theorem lemma_3_14_main :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ D : ℕ, 0 < D → ∃ p : ℕ,
        LeastIntervalPrime D p ∧ Prints M (natCode D) (natCode p) (C * lg D) := by
  obtain ⟨P, K, hK, h⟩ := alg_exists
  refine ⟨toMachine (P.comp 0), K, by exact_mod_cast hK, fun D hD => ?_⟩
  obtain ⟨p, hp, s', he, ho⟩ := h D hD
  refine ⟨p, hp, prints_of_eval P _ _ _ _ ?_ (by positivity) s' he ho⟩
  have h1 := natLog_le_logb (D + 1) (by omega)
  have h2 : ((K * (Nat.log 2 (D + 1) + 1) : ℕ) : ℝ) ≤ (K : ℝ) * lg D := by
    unfold lg log₂
    rw [Real.logb] at h1
    push_cast at h1 ⊢
    have hK0 : (0 : ℝ) ≤ K := by positivity
    have := mul_le_mul_of_nonneg_left h1 hK0
    nlinarith
  exact Nat.cast_le.1 (h2.trans (Nat.le_ceil _))

end CatalyticTreeEval.Main.Supplement

open CatalyticTreeEval.Main CatalyticTreeEval.Main.Supplement

theorem solution :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ D : ℕ, 0 < D → ∃ p : ℕ,
        LeastIntervalPrime D p ∧ Prints M (natCode D) (natCode p) (C * lg D) :=
  CatalyticTreeEval.Main.Supplement.lemma_3_14_main
