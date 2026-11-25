-- Prove2me | solution 1 for DetDLP.m89_resettable_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T01:58:16.463063+00:00
-- url     : https://prove2.me/submissions/f00fd404-5319-41c9-9997-d4f940e5df91

import Mathlib
import Definitions.Def_DetDLP_Machine
import Definitions.Def_DetDLP_M89_CompileSpace
import Definitions.Def_DetDLP_M89_MachineComp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.M89Resettable

open DetDLP DetDLP.MachineComposition
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-! ## Section 1: Extensional `absCell` Tape Algebra & `RunsWithin` Length Bounds -/

section TapeHelpers

def absCell (t : Turing.Tape (Option Bool)) (p z : ℤ) : Option Bool :=
  t.nth (z - p)

@[simp] theorem absCell_self (t : Turing.Tape (Option Bool)) (p : ℤ) :
    absCell t p p = t.head := by
  simp [absCell, Turing.Tape.nth_zero]

@[simp] theorem absCell_move_left (t : Turing.Tape (Option Bool)) (p z : ℤ) :
    absCell (t.move .left) (p - 1) z = absCell t p z := by
  simp only [absCell, Turing.Tape.move_left_nth]
  congr 1; omega

@[simp] theorem absCell_move_right (t : Turing.Tape (Option Bool)) (p z : ℤ) :
    absCell (t.move .right) (p + 1) z = absCell t p z := by
  simp only [absCell, Turing.Tape.move_right_nth]
  congr 1; omega

@[simp] theorem absCell_write (t : Turing.Tape (Option Bool)) (sym : Option Bool) (p z : ℤ) :
    absCell (t.write sym) p z = if z = p then sym else absCell t p z := by
  simp only [absCell, Turing.Tape.write_nth]
  by_cases h : z = p
  · subst h; simp
  · have hsub : z - p ≠ 0 := sub_ne_zero.mpr h
    simp [h, hsub]

theorem tape_ext {t₁ t₂ : Turing.Tape (Option Bool)}
    (h : ∀ z : ℤ, t₁.nth z = t₂.nth z) : t₁ = t₂ := by
  rcases t₁ with ⟨h₁, L₁, R₁⟩
  rcases t₂ with ⟨h₂, L₂, R₂⟩
  have hh : h₁ = h₂ := h 0
  have hL : L₁ = L₂ := Turing.ListBlank.ext fun n => h (-(n + 1 : ℕ))
  have hR : R₁ = R₂ := Turing.ListBlank.ext fun n => h (n + 1 : ℕ)
  subst hh; subst hL; subst hR; rfl

theorem tape_ext_absCell {t₁ t₂ : Turing.Tape (Option Bool)} {p : ℤ}
    (h : ∀ z : ℤ, absCell t₁ p z = absCell t₂ p z) : t₁ = t₂ := by
  apply tape_ext
  intro k
  simpa [absCell] using h (p + k)

private theorem nth_mk₁_nil (k : ℤ) :
    (Turing.Tape.mk₁ ([] : List (Option Bool))).nth k = none := by
  cases k with
  | ofNat n =>
    change (Turing.Tape.mk₁ ([] : List (Option Bool))).nth (n : ℤ) = none
    rw [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk]
    rfl
  | negSucc n =>
    change (Turing.ListBlank.mk ([] : List (Option Bool))).nth n = none
    rw [Turing.ListBlank.nth_mk]
    rfl

theorem blank_iff_absCell {t : Turing.Tape (Option Bool)} {p : ℤ} :
    (∀ z : ℤ, absCell t p z = none) ↔ t = Turing.Tape.mk₁ [] := by
  constructor
  · intro h
    apply tape_ext_absCell (p := p)
    intro z
    rw [h z]
    symm
    exact nth_mk₁_nil (z - p)
  · rintro rfl z
    exact nth_mk₁_nil (z - p)

theorem nth_tape_mk₁_ne_none {l : List Bool} {z : ℤ}
    (h : (Turing.Tape.mk₁ (l.map some)).nth z ≠ none) :
    0 ≤ z ∧ z.toNat < l.length := by
  cases z with
  | ofNat n =>
    change (Turing.Tape.mk₁ (l.map some)).nth (n : ℤ) ≠ none at h
    rw [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk] at h
    refine ⟨Int.natCast_nonneg n, ?_⟩
    by_contra hge
    have hle : (l.map some).length ≤ n := by simpa using Nat.le_of_not_lt hge
    exact h (List.getI_eq_default (l.map some) hle)
  | negSucc n =>
    exfalso; apply h
    change (Turing.ListBlank.mk ([] : List (Option Bool))).nth n = none
    rw [Turing.ListBlank.nth_mk]; rfl

theorem nth_tape_mk₁_get {l : List Bool} {n : ℕ} (hn : n < l.length) :
    (Turing.Tape.mk₁ (l.map some)).nth (n : ℤ) = some l[n] := by
  rw [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk,
    List.getI_eq_getElem _ (by simpa using hn)]
  simp

theorem absCell_mk₁_zero (w : List Bool) (z : ℤ) :
    absCell (Turing.Tape.mk₁ (w.map some)) 0 z =
      if h : 0 ≤ z ∧ z.toNat < w.length then some w[z.toNat] else none := by
  simp only [absCell, sub_zero]
  split_ifs with h
  · have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg h.1
    calc
      (Turing.Tape.mk₁ (w.map some)).nth z = (Turing.Tape.mk₁ (w.map some)).nth (z.toNat : ℤ) := by
        rw [hcast]
      _ = some w[z.toNat] := nth_tape_mk₁_get h.2
  · by_contra hne
    exact h (nth_tape_mk₁_ne_none hne)

def IsWordAt (t : Turing.Tape (Option Bool)) (p : ℤ) (w : List Bool) : Prop :=
  ∀ z : ℤ, absCell t p z = if h : 0 ≤ z ∧ z.toNat < w.length then some w[z.toNat] else none

theorem isWordAt_zero_iff (t : Turing.Tape (Option Bool)) (w : List Bool) :
    IsWordAt t 0 w ↔ t = Turing.Tape.mk₁ (w.map some) := by
  constructor
  · intro h
    apply tape_ext_absCell (p := 0)
    intro z
    rw [h z, absCell_mk₁_zero]
  · rintro rfl z
    exact absCell_mk₁_zero w z

def TapeSupportBound {M : PrimitiveMachine} (c : LocatedCfg M) : Prop :=
  ∀ (i : Fin M.tapeCount) (z : ℤ),
    absCell (c.config.tapes i) (c.position i) z ≠ none →
      c.lower i ≤ z ∧ z ≤ c.upper i

theorem tapeSupportBound_init (M : PrimitiveMachine) (input : List Bool) :
    TapeSupportBound (locatedInit M input) := by
  intro i z hz
  simp only [locatedInit, absCell, sub_zero, Int.ofNat_eq_natCast] at hz ⊢
  by_cases hi : i = M.inputTape
  · subst hi
    simp only [PrimitiveMachine.init, ↓reduceIte] at hz ⊢
    rcases nth_tape_mk₁_ne_none hz with ⟨hz0, hlt⟩
    exact ⟨hz0, by omega⟩
  · exfalso
    simp only [PrimitiveMachine.init, hi, ↓reduceIte] at hz
    rcases nth_tape_mk₁_ne_none (l := []) hz with ⟨_, hlt⟩
    simp at hlt

theorem tapeSupportBound_step {M : PrimitiveMachine} {c d : LocatedCfg M}
    (hw : LocatedWellFormed c) (hs : TapeSupportBound c)
    (hstep : locatedStep M c = some d) : TapeSupportBound d := by
  unfold locatedStep at hstep
  cases hcstep : M.step c.config with
  | none => simp [hcstep] at hstep
  | some cfg' =>
    have hd : c.monitor cfg' = d := by simpa [hcstep] using hstep
    subst d
    rcases c with ⟨⟨st, tapes⟩, pos, low, upp⟩
    cases st with
    | inl b => simp [PrimitiveMachine.step] at hcstep
    | inr q =>
      simp only [PrimitiveMachine.step] at hcstep
      cases htr : M.transition q (tapes (M.scan q)).head with
      | inl ans =>
        simp only [htr, Option.some.injEq] at hcstep
        subst hcstep
        intro i z hz
        simpa [LocatedCfg.monitor, htr, absCell] using
          hs i z (by simpa [LocatedCfg.monitor, htr, absCell] using hz)
      | inr qa =>
        rcases qa with ⟨q', act⟩
        simp only [htr, Option.some.injEq] at hcstep
        subst hcstep
        intro i z hz
        by_cases hi : i = M.scan q
        · subst i
          cases act with
          | move dir =>
            cases dir with
            | left =>
              simp only [LocatedCfg.monitor, Sum.elim_inr, htr, Function.update_self,
                headDisplacement] at hz ⊢
              change absCell ((tapes (M.scan q)).move .left) (pos (M.scan q) - 1) z ≠ none at hz
              rw [absCell_move_left] at hz
              rcases hs (M.scan q) z hz with ⟨hl, hu⟩
              exact ⟨le_trans (min_le_left _ _) hl, le_trans hu (le_max_left _ _)⟩
            | right =>
              simp only [LocatedCfg.monitor, Sum.elim_inr, htr, Function.update_self,
                headDisplacement] at hz ⊢
              change absCell ((tapes (M.scan q)).move .right) (pos (M.scan q) + 1) z ≠ none at hz
              rw [absCell_move_right] at hz
              rcases hs (M.scan q) z hz with ⟨hl, hu⟩
              exact ⟨le_trans (min_le_left _ _) hl, le_trans hu (le_max_left _ _)⟩
          | write sym =>
            simp only [LocatedCfg.monitor, Sum.elim_inr, htr, Function.update_self,
              headDisplacement, add_zero] at hz ⊢
            change absCell ((tapes (M.scan q)).write sym) (pos (M.scan q)) z ≠ none at hz
            rw [absCell_write] at hz
            by_cases hzp : z = pos (M.scan q)
            · subst z
              rcases hw (M.scan q) with ⟨hl, hu⟩
              exact ⟨le_trans (min_le_left _ _) hl, le_trans hu (le_max_left _ _)⟩
            · simp only [hzp, ↓reduceIte] at hz
              rcases hs (M.scan q) z hz with ⟨hl, hu⟩
              exact ⟨le_trans (min_le_left _ _) hl, le_trans hu (le_max_left _ _)⟩
        · simp only [LocatedCfg.monitor, Sum.elim_inr, htr, Function.update_of_ne hi] at hz ⊢
          exact hs i z hz

theorem tapeSupportBound_trace {M : PrimitiveMachine} {input : List Bool}
    {n : ℕ} {c : LocatedCfg M} (ht : Computation.Trace (locatedStep M) n (locatedInit M input) c) :
    TapeSupportBound c := by
  have aux : ∀ {a b : LocatedCfg M} {m : ℕ},
      LocatedWellFormed a → TapeSupportBound a → Computation.Trace (locatedStep M) m a b →
      TapeSupportBound b := by
    intro a b m hw hs htr
    induction htr with
    | refl => exact hs
    | cons hst _ ih => exact ih (locatedWellFormed_step hw hst) (tapeSupportBound_step hw hs hst)
  exact aux (locatedWellFormed_init M input) (tapeSupportBound_init M input) ht

theorem runsWithin_input_length_le {M : PrimitiveMachine} {out : Fin M.tapeCount}
    {input output : List Bool} {τ σ : ℝ} (h : RunsWithin M out input output τ σ) :
    (input.length : ℝ) ≤ σ := by
  rcases h with ⟨n, c, _, _, _, _, hs⟩
  have h0 := hs 0 (locatedInit M input) (Nat.zero_le n) (.refl _)
  have hlen : input.length ≤ visitedSpace (locatedInit M input) := by
    by_cases h0len : input.length = 0
    · omega
    · have hterm := Finset.single_le_sum (f := fun i : Fin M.tapeCount =>
        ((locatedInit M input).upper i - (locatedInit M input).lower i + 1).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ M.inputTape)
      have hval : ((locatedInit M input).upper M.inputTape - (locatedInit M input).lower M.inputTape + 1).toNat =
          input.length := by
        simp only [locatedInit, ↓reduceIte, Int.ofNat_eq_natCast]; omega
      change ((locatedInit M input).upper M.inputTape - (locatedInit M input).lower M.inputTape + 1).toNat ≤
        visitedSpace (locatedInit M input) at hterm
      omega
  exact le_trans (by exact_mod_cast hlen) h0

theorem runsWithin_output_length_le {M : PrimitiveMachine} {out : Fin M.tapeCount}
    {input output : List Bool} {τ σ : ℝ} (h : RunsWithin M out input output τ σ) :
    (output.length : ℝ) ≤ σ := by
  rcases h with ⟨n, c, htr, _, hout, _, hs⟩
  have hbound := hs n c le_rfl htr
  have hsup := tapeSupportBound_trace htr
  have hlen : output.length ≤ visitedSpace c := by
    by_cases h0len : output.length = 0
    · omega
    · have h0lt : 0 < output.length := Nat.pos_of_ne_zero h0len
      have hlt : output.length - 1 < output.length := by omega
      have hne0 : (c.config.tapes out).nth (0 : ℤ) ≠ none := by
        rw [hout, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, nth_tape_mk₁_get h0lt]; simp
      have hne1 : (c.config.tapes out).nth ((output.length - 1 : ℕ) : ℤ) ≠ none := by
        rw [hout, nth_tape_mk₁_get hlt]; simp
      have hl0 := (hsup out (c.position out) (by simpa [absCell] using hne0)).1
      have hu1 := (hsup out (c.position out + (output.length - 1 : ℕ))
        (by simpa [absCell] using hne1)).2
      have hspan : output.length ≤ (c.upper out - c.lower out + 1).toNat := by omega
      have hterm := Finset.single_le_sum (f := fun i : Fin M.tapeCount =>
        (c.upper i - c.lower i + 1).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ out)
      exact hspan.trans hterm
  exact le_trans (by exact_mod_cast hlen) hbound

theorem loc_ext {M : PrimitiveMachine} {a b : LocatedCfg M}
    (hs : a.config.state = b.config.state)
    (ht : ∀ i, a.config.tapes i = b.config.tapes i)
    (hp : ∀ i, a.position i = b.position i)
    (hl : ∀ i, a.lower i = b.lower i)
    (hu : ∀ i, a.upper i = b.upper i) : a = b := by
  rcases a with ⟨⟨sa, ta⟩, pa, la, ua⟩
  rcases b with ⟨⟨sb, tb⟩, pb, lb, ub⟩
  dsimp at hs ht hp hl hu
  subst hs
  have htf : ta = tb := funext ht
  have hpf : pa = pb := funext hp
  have hlf : la = lb := funext hl
  have huf : ua = ub := funext hu
  subst htf; subst hpf; subst hlf; subst huf; rfl

end TapeHelpers

/-! ## Section 2: Direct Instruction Machine Combinator `COp` -/

section COpMachine

inductive COp (Q : Type) (T : Type) where
  | halt (b : Bool)
  | act (t : T) (stmt : Turing.TM0.Stmt (Option Bool)) (next : Q)
  | branch (t : T) (next : Option Bool → Q)
  | raw (t : T) (tr : Option Bool → Bool ⊕ (Q × Turing.TM0.Stmt (Option Bool)))

section Build
variable {Q T : Type} [Fintype Q] [Fintype T]

noncomputable def cMachine (ops : Q → COp Q T) (start : Q) (inT : T) : PrimitiveMachine where
  tapeCount := Fintype.card T
  stateCount := Fintype.card Q
  inputTape := Fintype.equivFin T inT
  start := Fintype.equivFin Q start
  scan qIdx :=
    let q := (Fintype.equivFin Q).symm qIdx
    match ops q with
    | .halt _ => Fintype.equivFin T inT
    | .act t _ _ => Fintype.equivFin T t
    | .branch t _ => Fintype.equivFin T t
    | .raw t _ => Fintype.equivFin T t
  transition qIdx sym :=
    let q := (Fintype.equivFin Q).symm qIdx
    match ops q with
    | .halt b => .inl b
    | .act _ stmt next => .inr (Fintype.equivFin Q next, stmt)
    | .branch _ next => .inr (Fintype.equivFin Q (next sym), .write sym)
    | .raw _ tr =>
      match tr sym with
      | .inl b => .inl b
      | .inr (next, stmt) => .inr (Fintype.equivFin Q next, stmt)

noncomputable def packTapes (T : Type) [Fintype T] {α : Type} (f : T → α) : Fin (Fintype.card T) → α :=
  f ∘ (Fintype.equivFin T).symm

@[simp] theorem packTapes_apply {T : Type} [Fintype T] {α : Type} (f : T → α) (t : T) :
    packTapes T f (Fintype.equivFin T t) = f t := by
  simp [packTapes]

theorem packTapes_update {T : Type} [DecidableEq T] [Fintype T] {α : Type}
    (f : T → α) (t : T) (v : α) :
    Function.update (packTapes T f) (Fintype.equivFin T t) v =
      packTapes T (Function.update f t v) := by
  funext j
  obtain ⟨i, rfl⟩ := (Fintype.equivFin T).surjective j
  by_cases h : i = t
  · subst h; simp
  · simp [Function.update_of_ne h, Function.update_of_ne ((Fintype.equivFin T).injective.ne h)]

noncomputable def cCfg (ops : Q → COp Q T) (start : Q) (inT : T)
    (q : Bool ⊕ Q) (t : T → Turing.Tape (Option Bool)) (p l u : T → ℤ) :
    LocatedCfg (cMachine ops start inT) where
  config := ⟨q.map id (Fintype.equivFin Q), packTapes T t⟩
  position := packTapes T p
  lower := packTapes T l
  upper := packTapes T u

theorem cStep_halt {ops : Q → COp Q T} {start q : Q} {inT : T} {b : Bool}
    (h : ops q = .halt b) (t : T → Turing.Tape (Option Bool)) (p l u : T → ℤ) :
    locatedStep (cMachine ops start inT) (cCfg ops start inT (.inr q) t p l u) =
      some (cCfg ops start inT (.inl b) t p l u) := by
  simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, cMachine, cCfg, h]

theorem cStep_write [DecidableEq T] {ops : Q → COp Q T} {start q q' : Q} {inT k : T}
    {sym : Option Bool} (h : ops q = .act k (.write sym) q')
    (t : T → Turing.Tape (Option Bool)) (p l u : T → ℤ) (hw : l k ≤ p k ∧ p k ≤ u k) :
    locatedStep (cMachine ops start inT) (cCfg ops start inT (.inr q) t p l u) =
      some (cCfg ops start inT (.inr q') (Function.update t k ((t k).write sym)) p l u) := by
  simp only [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, cMachine, cCfg,
    Sum.map_inr, Sum.elim_inr, Equiv.symm_apply_apply, h, packTapes_apply, headDisplacement,
    Option.map_some, add_zero]
  apply congrArg some
  apply loc_ext
  · rfl
  · intro i
    obtain ⟨a, rfl⟩ := (Fintype.equivFin T).surjective i
    by_cases ha : a = k
    · subst ha; simp [Function.update, packTapes_apply]
    · simp [Function.update, (Fintype.equivFin T).injective.ne ha, ha, packTapes_apply]
  · intro i
    obtain ⟨a, rfl⟩ := (Fintype.equivFin T).surjective i
    by_cases ha : a = k <;> simp [Function.update, ha, packTapes_apply]
  · intro i
    obtain ⟨a, rfl⟩ := (Fintype.equivFin T).surjective i
    by_cases ha : a = k
    · subst ha; simp [Function.update, packTapes_apply, min_eq_left hw.1]
    · simp [Function.update, (Fintype.equivFin T).injective.ne ha, packTapes_apply]
  · intro i
    obtain ⟨a, rfl⟩ := (Fintype.equivFin T).surjective i
    by_cases ha : a = k
    · subst ha; simp [Function.update, packTapes_apply, max_eq_left hw.2]
    · simp [Function.update, (Fintype.equivFin T).injective.ne ha, packTapes_apply]

theorem cStep_move [DecidableEq T] {ops : Q → COp Q T} {start q q' : Q} {inT k : T}
    {dir : Turing.Dir} (h : ops q = .act k (.move dir) q')
    (t : T → Turing.Tape (Option Bool)) (p l u : T → ℤ) :
    let pos' := p k + headDisplacement (.move dir)
    locatedStep (cMachine ops start inT) (cCfg ops start inT (.inr q) t p l u) =
      some (cCfg ops start inT (.inr q')
        (Function.update t k ((t k).move dir))
        (Function.update p k pos')
        (Function.update l k (min (l k) pos'))
        (Function.update u k (max (u k) pos'))) := by
  simp only [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, cMachine, cCfg,
    Sum.map_inr, Sum.elim_inr, Equiv.symm_apply_apply, h, packTapes_apply, Option.map_some,
    packTapes_update]

theorem cStep_branch {ops : Q → COp Q T} {start q : Q} {inT k : T}
    {next : Option Bool → Q} (h : ops q = .branch k next)
    (t : T → Turing.Tape (Option Bool)) (p l u : T → ℤ) (hw : l k ≤ p k ∧ p k ≤ u k) :
    locatedStep (cMachine ops start inT) (cCfg ops start inT (.inr q) t p l u) =
      some (cCfg ops start inT (.inr (next (t k).head)) t p l u) := by
  simp only [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, cMachine, cCfg,
    Sum.map_inr, Sum.elim_inr, Equiv.symm_apply_apply, h, packTapes_apply, Turing.Tape.write_self,
    headDisplacement, Option.map_some, add_zero]
  apply congrArg some
  apply loc_ext
  · rfl
  · intro i
    obtain ⟨a, rfl⟩ := (Fintype.equivFin T).surjective i
    by_cases ha : a = k
    · subst ha; simp [Function.update, packTapes_apply]
    · simp [Function.update, (Fintype.equivFin T).injective.ne ha, packTapes_apply]
  · intro i
    obtain ⟨a, rfl⟩ := (Fintype.equivFin T).surjective i
    by_cases ha : a = k
    · subst ha; simp [Function.update, packTapes_apply]
    · simp [Function.update, (Fintype.equivFin T).injective.ne ha, packTapes_apply]
  · intro i
    obtain ⟨a, rfl⟩ := (Fintype.equivFin T).surjective i
    by_cases ha : a = k
    · subst ha; simp [Function.update, packTapes_apply, min_eq_left hw.1]
    · simp [Function.update, (Fintype.equivFin T).injective.ne ha, packTapes_apply]
  · intro i
    obtain ⟨a, rfl⟩ := (Fintype.equivFin T).surjective i
    by_cases ha : a = k
    · subst ha; simp [Function.update, packTapes_apply, max_eq_left hw.2]
    · simp [Function.update, (Fintype.equivFin T).injective.ne ha, packTapes_apply]

theorem cStep_raw_move [DecidableEq T] {ops : Q → COp Q T} {start q q' : Q} {inT k : T}
    {tr : Option Bool → Bool ⊕ (Q × Turing.TM0.Stmt (Option Bool))}
    {dir : Turing.Dir} (h : ops q = .raw k tr)
    (t : T → Turing.Tape (Option Bool)) (p l u : T → ℤ)
    (htr : tr (t k).head = .inr (q', .move dir)) :
    let pos' := p k + headDisplacement (.move dir)
    locatedStep (cMachine ops start inT) (cCfg ops start inT (.inr q) t p l u) =
      some (cCfg ops start inT (.inr q')
        (Function.update t k ((t k).move dir))
        (Function.update p k pos')
        (Function.update l k (min (l k) pos'))
        (Function.update u k (max (u k) pos'))) := by
  simp only [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, cMachine, cCfg,
    Sum.map_inr, Sum.elim_inr, Equiv.symm_apply_apply, h, packTapes_apply, htr, Option.map_some,
    packTapes_update]

theorem cStep_raw_write [DecidableEq T] {ops : Q → COp Q T} {start q q' : Q} {inT k : T}
    {tr : Option Bool → Bool ⊕ (Q × Turing.TM0.Stmt (Option Bool))}
    {sym : Option Bool} (h : ops q = .raw k tr)
    (t : T → Turing.Tape (Option Bool)) (p l u : T → ℤ)
    (htr : tr (t k).head = .inr (q', .write sym)) (hw : l k ≤ p k ∧ p k ≤ u k) :
    locatedStep (cMachine ops start inT) (cCfg ops start inT (.inr q) t p l u) =
      some (cCfg ops start inT (.inr q') (Function.update t k ((t k).write sym)) p l u) := by
  simp only [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, cMachine, cCfg,
    Sum.map_inr, Sum.elim_inr, Equiv.symm_apply_apply, h, packTapes_apply, htr, headDisplacement,
    Option.map_some, add_zero]
  apply congrArg some
  apply loc_ext
  · rfl
  · intro i
    obtain ⟨a, rfl⟩ := (Fintype.equivFin T).surjective i
    by_cases ha : a = k
    · subst ha; simp [Function.update, packTapes_apply]
    · simp [Function.update, (Fintype.equivFin T).injective.ne ha, ha, packTapes_apply]
  · intro i
    obtain ⟨a, rfl⟩ := (Fintype.equivFin T).surjective i
    by_cases ha : a = k <;> simp [Function.update, ha, packTapes_apply]
  · intro i
    obtain ⟨a, rfl⟩ := (Fintype.equivFin T).surjective i
    by_cases ha : a = k
    · subst ha; simp [Function.update, packTapes_apply, min_eq_left hw.1]
    · simp [Function.update, (Fintype.equivFin T).injective.ne ha, packTapes_apply]
  · intro i
    obtain ⟨a, rfl⟩ := (Fintype.equivFin T).surjective i
    by_cases ha : a = k
    · subst ha; simp [Function.update, packTapes_apply, max_eq_left hw.2]
    · simp [Function.update, (Fintype.equivFin T).injective.ne ha, packTapes_apply]

end Build

end COpMachine

/-! ## Section 3: Flat `RQ` State Encoding and `ResetBlock` Machine -/

section ResetBlock

abbrev RTape (t : ℕ) := Unit ⊕ Fin t ⊕ Fin t

abbrev tIO {t : ℕ} : RTape t := .inl ()
abbrev tData {t : ℕ} (j : Fin t) : RTape t := .inr (.inl j)
abbrev tMark {t : ℕ} (j : Fin t) : RTape t := .inr (.inr j)

abbrev RQ (t s : ℕ) := Fin 30 ⊕ (Fin t × Fin 24) ⊕ Fin s ⊕ (Fin t × Fin s × Fin 4)

abbrev qCopyInCheck {t s : ℕ} : RQ t s := .inl 0
abbrev qCopyInWriteD {t s : ℕ} (b : Bool) : RQ t s := .inl (if b then 1 else 2)
abbrev qCopyInCheckM {t s : ℕ} : RQ t s := .inl 3
abbrev qCopyInWriteM {t s : ℕ} : RQ t s := .inl 4
abbrev qCopyInAdvIO {t s : ℕ} : RQ t s := .inl 5
abbrev qCopyInAdvD {t s : ℕ} : RQ t s := .inl 6
abbrev qCopyInAdvM {t s : ℕ} : RQ t s := .inl 7
abbrev qEraseIOStart {t s : ℕ} : RQ t s := .inl 8
abbrev qEraseIOCheck {t s : ℕ} : RQ t s := .inl 9
abbrev qEraseIOWrite {t s : ℕ} : RQ t s := .inl 10
abbrev qEraseIORight {t s : ℕ} : RQ t s := .inl 11
abbrev qRewDStart {t s : ℕ} : RQ t s := .inl 12
abbrev qRewDCheck {t s : ℕ} : RQ t s := .inl 13
abbrev qRewDRight {t s : ℕ} : RQ t s := .inl 14
abbrev qRewMStart {t s : ℕ} : RQ t s := .inl 15
abbrev qRewMCheck {t s : ℕ} : RQ t s := .inl 16
abbrev qRewMRight {t s : ℕ} : RQ t s := .inl 17
abbrev qOutRead {t s : ℕ} : RQ t s := .inl 18
abbrev qOutWriteIO {t s : ℕ} (b : Bool) : RQ t s := .inl (if b then 19 else 20)
abbrev qOutAdvIO {t s : ℕ} : RQ t s := .inl 21
abbrev qOutAdvD {t s : ℕ} : RQ t s := .inl 22
abbrev qOutAdvM {t s : ℕ} : RQ t s := .inl 23
abbrev qOutCheckM {t s : ℕ} : RQ t s := .inl 24
abbrev qOutWriteM {t s : ℕ} : RQ t s := .inl 25
abbrev qRewIOStart {t s : ℕ} : RQ t s := .inl 26
abbrev qRewIOCheck {t s : ℕ} : RQ t s := .inl 27
abbrev qRewIORight {t s : ℕ} : RQ t s := .inl 28
abbrev qDone {t s : ℕ} : RQ t s := .inl 29

abbrev qMarkZero {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 0))
abbrev qWipeS1Check {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 1))
abbrev qWipeS1AdvD {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 2))
abbrev qWipeS1AdvM {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 3))
abbrev qWipeS2BackD {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 4))
abbrev qWipeS2BackM {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 5))
abbrev qWipeS2Check {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 6))
abbrev qWipeS2ClrD {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 7))
abbrev qWipeS2ClrM {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 8))
abbrev qWipeS2StepD {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 9))
abbrev qWipeS2StepM {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 10))
abbrev qWipeS3Check {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 11))
abbrev qWipeS3StepD {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 12))
abbrev qWipeS3StepM {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 13))
abbrev qWipeS4FwdD {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 14))
abbrev qWipeS4FwdM {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 15))
abbrev qWipeS4Check {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 16))
abbrev qWipeS4ClrD {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 17))
abbrev qWipeS4ClrM {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 18))
abbrev qWipeS4StepD {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 19))
abbrev qWipeS4StepM {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 20))
abbrev qWipeClr0D {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 21))
abbrev qWipeClr0M {t s : ℕ} (j : Fin t) : RQ t s := .inr (.inl (j, 22))

abbrev qSim {t s : ℕ} (q : Fin s) : RQ t s := .inr (.inr (.inl q))
abbrev qSimMoveM {t s : ℕ} (j : Fin t) (q' : Fin s) (dir : Turing.Dir) : RQ t s :=
  .inr (.inr (.inr (j, q', match dir with | .left => 0 | .right => 1)))
abbrev qSimCheckM {t s : ℕ} (j : Fin t) (q' : Fin s) : RQ t s := .inr (.inr (.inr (j, q', 2)))
abbrev qSimWriteM {t s : ℕ} (j : Fin t) (q' : Fin s) : RQ t s := .inr (.inr (.inr (j, q', 3)))

def rOps (A : PrimitiveMachine) (outA : Fin A.tapeCount) :
    RQ A.tapeCount A.stateCount → COp (RQ A.tapeCount A.stateCount) (RTape A.tapeCount)
  | .inl idx => match idx.val with
    | 0 => .branch tIO fun | none => qEraseIOStart | some b => qCopyInWriteD b
    | 1 => .act (tData A.inputTape) (.write (some true)) qCopyInCheckM
    | 2 => .act (tData A.inputTape) (.write (some false)) qCopyInCheckM
    | 3 => .branch (tMark A.inputTape) fun | none => qCopyInWriteM | some _ => qCopyInAdvIO
    | 4 => .act (tMark A.inputTape) (.write (some true)) qCopyInAdvIO
    | 5 => .act tIO (.move .right) qCopyInAdvD
    | 6 => .act (tData A.inputTape) (.move .right) qCopyInAdvM
    | 7 => .act (tMark A.inputTape) (.move .right) qCopyInCheck
    | 8 => .act tIO (.move .left) qEraseIOCheck
    | 9 => .branch tIO fun | none => qEraseIORight | some _ => qEraseIOWrite
    | 10 => .act tIO (.write none) qEraseIOStart
    | 11 => .act tIO (.move .right) qRewDStart
    | 12 => .act (tData A.inputTape) (.move .left) qRewDCheck
    | 13 => .branch (tData A.inputTape) fun | none => qRewDRight | some _ => qRewDStart
    | 14 => .act (tData A.inputTape) (.move .right) qRewMStart
    | 15 => .act (tMark A.inputTape) (.move .left) qRewMCheck
    | 16 => .branch (tMark A.inputTape) fun | none => qRewMRight | some _ => qRewMStart
    | 17 => .act (tMark A.inputTape) (.move .right) (qSim A.start)
    | 18 => .branch (tData outA) fun | none => qRewIOStart | some b => qOutWriteIO b
    | 19 => .act tIO (.write (some true)) qOutAdvIO
    | 20 => .act tIO (.write (some false)) qOutAdvIO
    | 21 => .act tIO (.move .right) qOutAdvD
    | 22 => .act (tData outA) (.move .right) qOutAdvM
    | 23 => .act (tMark outA) (.move .right) qOutCheckM
    | 24 => .branch (tMark outA) fun | none => qOutWriteM | some _ => qOutRead
    | 25 => .act (tMark outA) (.write (some true)) qOutRead
    | 26 => .act tIO (.move .left) qRewIOCheck
    | 27 => .branch tIO fun | none => qRewIORight | some _ => qRewIOStart
    | 28 => .act tIO (.move .right) (qWipeS1Check ⟨0, Fin.pos A.inputTape⟩)
    | _ => .halt true
  | .inr (.inl (j, widx)) => match widx.val with
    | 0 =>
      let next := if h : j.val + 1 < A.tapeCount then qMarkZero ⟨j.val + 1, h⟩ else qCopyInCheck
      .act (tMark j) (.write (some false)) next
    | 1 => .branch (tMark j) fun | none => qWipeS2BackD j | some _ => qWipeS1AdvD j
    | 2 => .act (tData j) (.move .right) (qWipeS1AdvM j)
    | 3 => .act (tMark j) (.move .right) (qWipeS1Check j)
    | 4 => .act (tData j) (.move .left) (qWipeS2BackM j)
    | 5 => .act (tMark j) (.move .left) (qWipeS2Check j)
    | 6 => .branch (tMark j) fun | some true => qWipeS2ClrD j | _ => qWipeS3Check j
    | 7 => .act (tData j) (.write none) (qWipeS2ClrM j)
    | 8 => .act (tMark j) (.write none) (qWipeS2StepD j)
    | 9 => .act (tData j) (.move .left) (qWipeS2StepM j)
    | 10 => .act (tMark j) (.move .left) (qWipeS2Check j)
    | 11 => .branch (tMark j) fun | none => qWipeS4FwdD j | some _ => qWipeS3StepD j
    | 12 => .act (tData j) (.move .left) (qWipeS3StepM j)
    | 13 => .act (tMark j) (.move .left) (qWipeS3Check j)
    | 14 => .act (tData j) (.move .right) (qWipeS4FwdM j)
    | 15 => .act (tMark j) (.move .right) (qWipeS4Check j)
    | 16 => .branch (tMark j) fun | some true => qWipeS4ClrD j | _ => qWipeClr0D j
    | 17 => .act (tData j) (.write none) (qWipeS4ClrM j)
    | 18 => .act (tMark j) (.write none) (qWipeS4StepD j)
    | 19 => .act (tData j) (.move .right) (qWipeS4StepM j)
    | 20 => .act (tMark j) (.move .right) (qWipeS4Check j)
    | 21 => .act (tData j) (.write none) (qWipeClr0M j)
    | 22 =>
      let next := if h : j.val + 1 < A.tapeCount then qWipeS1Check ⟨j.val + 1, h⟩ else qDone
      .act (tMark j) (.write none) next
    | _ => .halt true
  | .inr (.inr (.inl q)) =>
    .raw (tData (A.scan q)) fun sym =>
      match A.transition q sym with
      | .inl _ => .inr (qOutRead, .write sym)
      | .inr (q', .write w) => .inr (qSim q', .write w)
      | .inr (q', .move dir) => .inr (qSimMoveM (A.scan q) q' dir, .move dir)
  | .inr (.inr (.inr (j, q', midx))) => match midx.val with
    | 0 => .act (tMark j) (.move .left) (qSimCheckM j q')
    | 1 => .act (tMark j) (.move .right) (qSimCheckM j q')
    | 2 => .branch (tMark j) fun | none => qSimWriteM j q' | some _ => qSim q'
    | _ => .act (tMark j) (.write (some true)) (qSim q')

def rStart (A : PrimitiveMachine) : RQ A.tapeCount A.stateCount :=
  qMarkZero ⟨0, Fin.pos A.inputTape⟩

noncomputable abbrev resetMachine (A : PrimitiveMachine) (outA : Fin A.tapeCount) : PrimitiveMachine :=
  cMachine (rOps A outA) (rStart A) tIO

def MarkExact (tm : Turing.Tape (Option Bool)) (p L U : ℤ) : Prop :=
  L ≤ 0 ∧ 0 ≤ U ∧ L ≤ p ∧ p ≤ U ∧
  ∀ z : ℤ, absCell tm p z = if z = 0 then some false else if L ≤ z ∧ z ≤ U then some true else none

def DataSupported (td : Turing.Tape (Option Bool)) (p L U : ℤ) : Prop :=
  ∀ z : ℤ, absCell td p z ≠ none → L ≤ z ∧ z ≤ U

section Phases
variable (A : PrimitiveMachine) (outA : Fin A.tapeCount)

private abbrev RCfg := RTape A.tapeCount → Turing.Tape (Option Bool)
private abbrev RPos := RTape A.tapeCount → ℤ

private theorem trace_prepend1 {α : Type} {step : α → Option α} {a b c : α} {n : ℕ}
    (h1 : step a = some b) (ht : Computation.Trace step n b c) :
    Computation.Trace step (1 + n) a c := by
  rw [Nat.add_comm]; exact .cons h1 ht

private theorem trace_prepend2 {α : Type} {step : α → Option α} {a b₁ b₂ c : α} {n : ℕ}
    (h1 : step a = some b₁) (h2 : step b₁ = some b₂)
    (ht : Computation.Trace step n b₂ c) :
    Computation.Trace step (2 + n) a c := by
  rw [show 2 + n = (n + 1) + 1 by omega]; exact .cons h1 (.cons h2 ht)

private theorem trace_prepend3 {α : Type} {step : α → Option α} {a b₁ b₂ b₃ c : α} {n : ℕ}
    (h1 : step a = some b₁) (h2 : step b₁ = some b₂) (h3 : step b₂ = some b₃)
    (ht : Computation.Trace step n b₃ c) :
    Computation.Trace step (3 + n) a c := by
  rw [show 3 + n = ((n + 1) + 1) + 1 by omega]; exact .cons h1 (.cons h2 (.cons h3 ht))

private theorem trace_prepend5 {α : Type} {step : α → Option α} {a b₁ b₂ b₃ b₄ b₅ c : α} {n : ℕ}
    (h1 : step a = some b₁) (h2 : step b₁ = some b₂) (h3 : step b₂ = some b₃)
    (h4 : step b₃ = some b₄) (h5 : step b₄ = some b₅)
    (ht : Computation.Trace step n b₅ c) :
    Computation.Trace step (5 + n) a c := by
  rw [show 5 + n = ((((n + 1) + 1) + 1) + 1) + 1 by omega]
  exact .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 ht))))

private theorem rStep_halt {q : RQ A.tapeCount A.stateCount} {b : Bool}
    (h : rOps A outA q = .halt b) (t : RCfg A) (p l u : RPos A) :
    locatedStep (resetMachine A outA) (cCfg (rOps A outA) (rStart A) tIO (.inr q) t p l u) =
      some (cCfg (rOps A outA) (rStart A) tIO (.inl b) t p l u) :=
  cStep_halt h t p l u

private theorem rStep_write {q q' : RQ A.tapeCount A.stateCount} {k : RTape A.tapeCount}
    {sym : Option Bool} (h : rOps A outA q = .act k (.write sym) q')
    (t : RCfg A) (p l u : RPos A) (hw : l k ≤ p k ∧ p k ≤ u k) :
    locatedStep (resetMachine A outA) (cCfg (rOps A outA) (rStart A) tIO (.inr q) t p l u) =
      some (cCfg (rOps A outA) (rStart A) tIO (.inr q') (Function.update t k ((t k).write sym)) p l u) :=
  cStep_write h t p l u hw

private theorem rStep_move_right {q q' : RQ A.tapeCount A.stateCount} {k : RTape A.tapeCount}
    (h : rOps A outA q = .act k (.move .right) q')
    (t : RCfg A) (p l u : RPos A) :
    locatedStep (resetMachine A outA) (cCfg (rOps A outA) (rStart A) tIO (.inr q) t p l u) =
      some (cCfg (rOps A outA) (rStart A) tIO (.inr q')
        (Function.update t k ((t k).move .right))
        (Function.update p k (p k + 1))
        (Function.update l k (min (l k) (p k + 1)))
        (Function.update u k (max (u k) (p k + 1)))) :=
  cStep_move h t p l u

private theorem rStep_move_left {q q' : RQ A.tapeCount A.stateCount} {k : RTape A.tapeCount}
    (h : rOps A outA q = .act k (.move .left) q')
    (t : RCfg A) (p l u : RPos A) :
    locatedStep (resetMachine A outA) (cCfg (rOps A outA) (rStart A) tIO (.inr q) t p l u) =
      some (cCfg (rOps A outA) (rStart A) tIO (.inr q')
        (Function.update t k ((t k).move .left))
        (Function.update p k (p k - 1))
        (Function.update l k (min (l k) (p k - 1)))
        (Function.update u k (max (u k) (p k - 1)))) := by
  have h0 := cStep_move (ops := rOps A outA) (start := rStart A) (inT := tIO) h t p l u
  have heq : p k + headDisplacement (Turing.TM0.Stmt.move Turing.Dir.left) = p k - 1 := by
    simp [headDisplacement]; omega
  dsimp only at h0
  rwa [heq] at h0

private theorem rStep_move {q q' : RQ A.tapeCount A.stateCount} {k : RTape A.tapeCount}
    {dir : Turing.Dir} (h : rOps A outA q = .act k (.move dir) q')
    (t : RCfg A) (p l u : RPos A) :
    let pos' := p k + headDisplacement (.move dir)
    locatedStep (resetMachine A outA) (cCfg (rOps A outA) (rStart A) tIO (.inr q) t p l u) =
      some (cCfg (rOps A outA) (rStart A) tIO (.inr q')
        (Function.update t k ((t k).move dir))
        (Function.update p k pos')
        (Function.update l k (min (l k) pos'))
        (Function.update u k (max (u k) pos'))) :=
  cStep_move h t p l u

private theorem rStep_branch {q : RQ A.tapeCount A.stateCount} {k : RTape A.tapeCount}
    {next : Option Bool → RQ A.tapeCount A.stateCount} (h : rOps A outA q = .branch k next)
    (t : RCfg A) (p l u : RPos A) (hw : l k ≤ p k ∧ p k ≤ u k) :
    locatedStep (resetMachine A outA) (cCfg (rOps A outA) (rStart A) tIO (.inr q) t p l u) =
      some (cCfg (rOps A outA) (rStart A) tIO (.inr (next (t k).head)) t p l u) :=
  cStep_branch h t p l u hw

private theorem rStep_raw_move {q q' : RQ A.tapeCount A.stateCount} {k : RTape A.tapeCount}
    {tr : Option Bool → Bool ⊕ (RQ A.tapeCount A.stateCount × Turing.TM0.Stmt (Option Bool))}
    {dir : Turing.Dir} (h : rOps A outA q = .raw k tr)
    (t : RCfg A) (p l u : RPos A)
    (htr : tr (t k).head = .inr (q', .move dir)) :
    let pos' := p k + headDisplacement (.move dir)
    locatedStep (resetMachine A outA) (cCfg (rOps A outA) (rStart A) tIO (.inr q) t p l u) =
      some (cCfg (rOps A outA) (rStart A) tIO (.inr q')
        (Function.update t k ((t k).move dir))
        (Function.update p k pos')
        (Function.update l k (min (l k) pos'))
        (Function.update u k (max (u k) pos'))) :=
  cStep_raw_move h t p l u htr

private theorem rStep_raw_write {q q' : RQ A.tapeCount A.stateCount} {k : RTape A.tapeCount}
    {tr : Option Bool → Bool ⊕ (RQ A.tapeCount A.stateCount × Turing.TM0.Stmt (Option Bool))}
    {sym : Option Bool} (h : rOps A outA q = .raw k tr)
    (t : RCfg A) (p l u : RPos A)
    (htr : tr (t k).head = .inr (q', .write sym)) (hw : l k ≤ p k ∧ p k ≤ u k) :
    locatedStep (resetMachine A outA) (cCfg (rOps A outA) (rStart A) tIO (.inr q) t p l u) =
      some (cCfg (rOps A outA) (rStart A) tIO (.inr q') (Function.update t k ((t k).write sym)) p l u) :=
  cStep_raw_write h t p l u htr hw

private theorem rOps_copyInWriteD (b : Bool) :
    rOps A outA (qCopyInWriteD b) = .act (tData A.inputTape) (.write (some b)) qCopyInCheckM := by
  cases b <;> rfl

private theorem rOps_outWriteIO (b : Bool) :
    rOps A outA (qOutWriteIO b) = .act tIO (.write (some b)) qOutAdvIO := by
  cases b <;> rfl

private theorem rOps_simMoveM (j : Fin A.tapeCount) (q' : Fin A.stateCount) (dir : Turing.Dir) :
    rOps A outA (qSimMoveM j q' dir) = .act (tMark j) (.move dir) (qSimCheckM j q') := by
  cases dir <;> rfl

private theorem rPhase_markZero (t : RCfg A) (p l u : RPos A)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r)
    (hp : ∀ j : Fin A.tapeCount, p (tMark j) = 0 ∧ t (tMark j) = Turing.Tape.mk₁ []) :
    ∃ t1 n,
      Computation.Trace (locatedStep (resetMachine A outA)) n
        (cCfg (rOps A outA) (rStart A) tIO (.inr (rStart A)) t p l u)
        (cCfg (rOps A outA) (rStart A) tIO (.inr qCopyInCheck) t1 p l u) ∧
      n = A.tapeCount ∧
      t1 tIO = t tIO ∧
      (∀ j, t1 (tData j) = t (tData j)) ∧
      (∀ j : Fin A.tapeCount, t1 (tMark j) = (t (tMark j)).write (some false)) := by
  have ind : ∀ (rem k : ℕ) (hk : k < A.tapeCount) (hrem : A.tapeCount - k = rem)
      (t' : RCfg A) (hp' : ∀ j : Fin A.tapeCount, k ≤ j.val → p (tMark j) = 0 ∧ t' (tMark j) = Turing.Tape.mk₁ []),
      ∃ t1 n,
        Computation.Trace (locatedStep (resetMachine A outA)) n
          (cCfg (rOps A outA) (rStart A) tIO (.inr (qMarkZero ⟨k, hk⟩)) t' p l u)
          (cCfg (rOps A outA) (rStart A) tIO (.inr qCopyInCheck) t1 p l u) ∧
        n = A.tapeCount - k ∧
        t1 tIO = t' tIO ∧
        (∀ j, t1 (tData j) = t' (tData j)) ∧
        (∀ j : Fin A.tapeCount, k ≤ j.val → t1 (tMark j) = (t' (tMark j)).write (some false)) ∧
        (∀ j : Fin A.tapeCount, j.val < k → t1 (tMark j) = t' (tMark j)) := by
    intro rem
    induction rem with
    | zero => intro k hk hrem; omega
    | succ r ih =>
      intro k hk hrem t' hp'
      by_cases hlt : k + 1 < A.tapeCount
      · have hs := rStep_write A outA
          (q := qMarkZero ⟨k, hk⟩) (q' := qMarkZero ⟨k + 1, hlt⟩)
          (k := tMark ⟨k, hk⟩) (sym := some false)
          (by simp [rOps, hlt]) t' p l u (hw (tMark ⟨k, hk⟩))
        let t_1 := Function.update t' (tMark ⟨k, hk⟩) ((t' (tMark ⟨k, hk⟩)).write (some false))
        have hp_1 : ∀ j : Fin A.tapeCount, k + 1 ≤ j.val → p (tMark j) = 0 ∧ t_1 (tMark j) = Turing.Tape.mk₁ [] := by
          intro j hj
          have hne : (tMark j : RTape A.tapeCount) ≠ tMark ⟨k, hk⟩ := by
            intro heq; have hval : j.val = k := congrArg Fin.val (Sum.inr.inj (Sum.inr.inj heq)); omega
          dsimp [t_1]; rw [Function.update_of_ne hne]
          exact hp' j (by omega)
        obtain ⟨t1, n1, htr, hn1, hio, hda, hge, hlt1⟩ := ih (k + 1) hlt (by omega) t_1 hp_1
        refine ⟨t1, n1 + 1, .cons hs htr, by omega, ?_, ?_, ?_, ?_⟩
        · dsimp [t_1] at hio; rw [hio, Function.update_of_ne (by simp)]
        · intro j; dsimp [t_1] at hda; rw [hda j, Function.update_of_ne (by simp)]
        · intro j hj
          by_cases hjk : j.val = k
          · have hjk' : j = ⟨k, hk⟩ := Fin.ext hjk
            subst j
            rw [hlt1 ⟨k, hk⟩ (by simp only []; omega)]
            dsimp [t_1]; rw [Function.update_self]
          · have hjgt : k + 1 ≤ j.val := by omega
            have hne : (tMark j : RTape A.tapeCount) ≠ tMark ⟨k, hk⟩ := by
              intro heq; exact hjk (congrArg Fin.val (Sum.inr.inj (Sum.inr.inj heq)))
            rw [hge j hjgt]; dsimp [t_1]; rw [Function.update_of_ne hne]
        · intro j hj
          have hne : (tMark j : RTape A.tapeCount) ≠ tMark ⟨k, hk⟩ := by
            intro heq; have hval : j.val = k := congrArg Fin.val (Sum.inr.inj (Sum.inr.inj heq)); omega
          rw [hlt1 j (by omega)]; dsimp [t_1]; rw [Function.update_of_ne hne]
      · have hs := rStep_write A outA
          (q := qMarkZero ⟨k, hk⟩) (q' := qCopyInCheck)
          (k := tMark ⟨k, hk⟩) (sym := some false)
          (by simp [rOps, hlt]) t' p l u (hw (tMark ⟨k, hk⟩))
        refine ⟨Function.update t' (tMark ⟨k, hk⟩) ((t' (tMark ⟨k, hk⟩)).write (some false)), 1,
          .cons hs (.refl _), by omega, by simp, fun j => by simp, ?_, ?_⟩
        · intro j hj
          have hjlt := j.isLt
          have hval : j.val = k := by omega
          have hjk : j = ⟨k, hk⟩ := Fin.ext hval
          subst j; simp
        · intro j hj
          have hne : (tMark j : RTape A.tapeCount) ≠ tMark ⟨k, hk⟩ := by
            intro heq; have hval : j.val = k := congrArg Fin.val (Sum.inr.inj (Sum.inr.inj heq)); omega
          rw [Function.update_of_ne hne]
  obtain ⟨t1, n, htr, hn, hio, hda, hge, _⟩ :=
    ind A.tapeCount 0 (Fin.pos A.inputTape) (Nat.sub_zero _) t (fun j _ => hp j)
  exact ⟨t1, n, htr, by simpa using hn, hio, hda, fun j => hge j (Nat.zero_le _)⟩

private theorem rPhase_copyIn (input : List Bool)
    (t : RCfg A) (p l u L_env U_env : RPos A)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r)
    (henv : ∀ r, L_env r ≤ l r ∧ u r ≤ U_env r)
    (hru : L_env tIO ≤ 0 ∧ (input.length : ℤ) ≤ U_env tIO ∧
           L_env (tData A.inputTape) ≤ 0 ∧ (input.length : ℤ) ≤ U_env (tData A.inputTape) ∧
           L_env (tMark A.inputTape) ≤ 0 ∧ (input.length : ℤ) ≤ U_env (tMark A.inputTape))
    (hpio : p tIO = 0) (hpD : p (tData A.inputTape) = 0) (hpM : p (tMark A.inputTape) = 0)
    (htio : IsWordAt (t tIO) 0 input)
    (htD : t (tData A.inputTape) = Turing.Tape.mk₁ [])
    (htM : t (tMark A.inputTape) = (Turing.Tape.mk₁ ([] : List (Option Bool))).write (some false)) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (resetMachine A outA)) n
        (cCfg (rOps A outA) (rStart A) tIO (.inr qCopyInCheck) t p l u)
        (cCfg (rOps A outA) (rStart A) tIO (.inr qEraseIOStart) t1 p1 l1 u1) ∧
      n ≤ 7 * input.length + 1 ∧
      (∀ r, r ≠ tIO → r ≠ tData A.inputTape → r ≠ tMark A.inputTape →
        t1 r = t r ∧ p1 r = p r ∧ l1 r = l r ∧ u1 r = u r) ∧
      IsWordAt (t1 tIO) (input.length : ℤ) input ∧
      p1 tIO = input.length ∧ p1 (tData A.inputTape) = input.length ∧ p1 (tMark A.inputTape) = input.length ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧
      (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) ∧
      (∀ z : ℤ, absCell (t1 (tData A.inputTape)) input.length z =
        if h : 0 ≤ z ∧ z.toNat < input.length then some input[z.toNat] else none) ∧
      (∀ z : ℤ, absCell (t1 (tMark A.inputTape)) input.length z =
        if z = 0 then some false else if 1 ≤ z ∧ z < (input.length : ℤ) then some true else none) := by
  have ind : ∀ (rem k : ℕ) (hk : k ≤ input.length) (hrem : input.length - k = rem)
      (t' : RCfg A) (p' l' u' : RPos A)
      (hw' : ∀ r, l' r ≤ p' r ∧ p' r ≤ u' r)
      (henv' : ∀ r, L_env r ≤ l' r ∧ u' r ≤ U_env r)
      (hpio' : p' tIO = k) (hpD' : p' (tData A.inputTape) = k) (hpM' : p' (tMark A.inputTape) = k)
      (htio' : IsWordAt (t' tIO) (k : ℤ) input)
      (htD' : ∀ z : ℤ, absCell (t' (tData A.inputTape)) (k : ℤ) z =
        if h : 0 ≤ z ∧ z.toNat < k then some input[z.toNat] else none)
      (htM' : ∀ z : ℤ, absCell (t' (tMark A.inputTape)) (k : ℤ) z =
        if z = 0 then some false else if 1 ≤ z ∧ z < (k : ℤ) then some true else none),
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (resetMachine A outA)) n
          (cCfg (rOps A outA) (rStart A) tIO (.inr qCopyInCheck) t' p' l' u')
          (cCfg (rOps A outA) (rStart A) tIO (.inr qEraseIOStart) t1 p1 l1 u1) ∧
        n ≤ 7 * rem + 1 ∧
        (∀ r, r ≠ tIO → r ≠ tData A.inputTape → r ≠ tMark A.inputTape →
          t1 r = t' r ∧ p1 r = p' r ∧ l1 r = l' r ∧ u1 r = u' r) ∧
        IsWordAt (t1 tIO) (input.length : ℤ) input ∧
        p1 tIO = input.length ∧ p1 (tData A.inputTape) = input.length ∧ p1 (tMark A.inputTape) = input.length ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧
        (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) ∧
        (∀ z : ℤ, absCell (t1 (tData A.inputTape)) input.length z =
          if h : 0 ≤ z ∧ z.toNat < input.length then some input[z.toNat] else none) ∧
        (∀ z : ℤ, absCell (t1 (tMark A.inputTape)) input.length z =
          if z = 0 then some false else if 1 ≤ z ∧ z < (input.length : ℤ) then some true else none) := by
    intro rem
    induction rem with
    | zero =>
      intro k hk hrem t' p' l' u' hw' henv' hpio' hpD' hpM' htio' htD' htM'
      have hkeq : k = input.length := by omega
      subst hkeq
      have hhead : (t' tIO).head = none := by
        rw [← absCell_self (t' tIO) (p' tIO), hpio', htio']; simp
      have hs := rStep_branch A outA
        (q := qCopyInCheck) (k := tIO) rfl t' p' l' u' (hw' tIO)
      rw [hhead] at hs
      exact ⟨t', p', l', u', 1, .cons hs (.refl _), le_rfl, fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩,
        htio', hpio', hpD', hpM', hw', henv', htD', htM'⟩
    | succ r ih =>
      intro k hk hrem t' p' l' u' hw' henv' hpio' hpD' hpM' htio' htD' htM'
      have hlt : k < input.length := by omega
      let b := input[k]
      have hheadIO : (t' tIO).head = some b := by
        rw [← absCell_self (t' tIO) (p' tIO), hpio', htio']; simp [b, hlt]
      have hs0 := rStep_branch A outA
        (q := qCopyInCheck) (k := tIO) rfl t' p' l' u' (hw' tIO)
      rw [hheadIO] at hs0
      have hs1 := rStep_write A outA
        (q := qCopyInWriteD b) (q' := qCopyInCheckM) (k := tData A.inputTape) (sym := some b)
        (rOps_copyInWriteD A outA b) t' p' l' u' (hw' (tData A.inputTape))
      let t_1 := Function.update t' (tData A.inputTape) ((t' (tData A.inputTape)).write (some b))
      have hs2 := rStep_branch A outA
        (q := qCopyInCheckM) (k := tMark A.inputTape) rfl t_1 p' l' u' (hw' (tMark A.inputTape))
      have hheadM : (t_1 (tMark A.inputTape)).head = (if k = 0 then some false else none) := by
        have hne : (tMark A.inputTape : RTape A.tapeCount) ≠ tData A.inputTape := by simp
        change (Function.update t' (tData A.inputTape) _ (tMark A.inputTape)).head = _
        rw [Function.update_of_ne hne, ← absCell_self (t' (tMark A.inputTape)) (p' (tMark A.inputTape)),
          hpM', htM']
        by_cases hk0 : k = 0 <;> simp [hk0]
      have hM_branch : Computation.Trace (locatedStep (resetMachine A outA)) (if k = 0 then 1 else 2)
          (cCfg (rOps A outA) (rStart A) tIO (.inr qCopyInCheckM) t_1 p' l' u')
          (cCfg (rOps A outA) (rStart A) tIO (.inr qCopyInAdvIO)
            (if k = 0 then t_1 else Function.update t_1 (tMark A.inputTape) ((t_1 (tMark A.inputTape)).write (some true)))
            p' l' u') := by
        by_cases hk0 : k = 0
        · rw [if_pos hk0, if_pos hk0]; rw [hheadM, if_pos hk0] at hs2; exact .cons hs2 (.refl _)
        · rw [if_neg hk0, if_neg hk0]; rw [hheadM, if_neg hk0] at hs2
          have hs3 := rStep_write A outA
            (q := qCopyInWriteM) (q' := qCopyInAdvIO) (k := tMark A.inputTape) (sym := some true) rfl
            t_1 p' l' u' (hw' (tMark A.inputTape))
          exact .cons hs2 (.cons hs3 (.refl _))
      let t_2 := if k = 0 then t_1 else
        Function.update t_1 (tMark A.inputTape) ((t_1 (tMark A.inputTape)).write (some true))
      have hs4 := rStep_move_right A outA
        (q := qCopyInAdvIO) (q' := qCopyInAdvD) (k := tIO) rfl t_2 p' l' u'
      let p_4 := Function.update p' tIO (p' tIO + 1)
      let l_4 := Function.update l' tIO (min (l' tIO) (p' tIO + 1))
      let u_4 := Function.update u' tIO (max (u' tIO) (p' tIO + 1))
      let t_4 := Function.update t_2 tIO ((t_2 tIO).move .right)
      have hs5 := rStep_move_right A outA
        (q := qCopyInAdvD) (q' := qCopyInAdvM) (k := tData A.inputTape) rfl t_4 p_4 l_4 u_4
      let p_5 := Function.update p_4 (tData A.inputTape) (p_4 (tData A.inputTape) + 1)
      let l_5 := Function.update l_4 (tData A.inputTape) (min (l_4 (tData A.inputTape)) (p_4 (tData A.inputTape) + 1))
      let u_5 := Function.update u_4 (tData A.inputTape) (max (u_4 (tData A.inputTape)) (p_4 (tData A.inputTape) + 1))
      let t_5 := Function.update t_4 (tData A.inputTape) ((t_4 (tData A.inputTape)).move .right)
      have hs6 := rStep_move_right A outA
        (q := qCopyInAdvM) (q' := qCopyInCheck) (k := tMark A.inputTape) rfl t_5 p_5 l_5 u_5
      let p_6 := Function.update p_5 (tMark A.inputTape) (p_5 (tMark A.inputTape) + 1)
      let l_6 := Function.update l_5 (tMark A.inputTape) (min (l_5 (tMark A.inputTape)) (p_5 (tMark A.inputTape) + 1))
      let u_6 := Function.update u_5 (tMark A.inputTape) (max (u_5 (tMark A.inputTape)) (p_5 (tMark A.inputTape) + 1))
      let t_6 := Function.update t_5 (tMark A.inputTape) ((t_5 (tMark A.inputTape)).move .right)
      have hw_6 : ∀ r', l_6 r' ≤ p_6 r' ∧ p_6 r' ≤ u_6 r' := by
        intro r'
        rcases r' with _ | j | j
        · simp [p_6, l_6, u_6, p_5, l_5, u_5, p_4, l_4, u_4]
        · by_cases hj : j = A.inputTape
          · subst j; simp [p_6, l_6, u_6, p_5, l_5, u_5, p_4, l_4, u_4]
          · simp [p_6, l_6, u_6, p_5, l_5, u_5, p_4, l_4, u_4, hj, hw' (tData j)]
        · by_cases hj : j = A.inputTape
          · subst j; simp [p_6, l_6, u_6, p_5, l_5, u_5, p_4, l_4, u_4]
          · simp [p_6, l_6, u_6, p_5, l_5, u_5, p_4, l_4, u_4, hj, hw' (tMark j)]
      have henv_6 : ∀ r', L_env r' ≤ l_6 r' ∧ u_6 r' ≤ U_env r' := by
        intro r'
        rcases r' with _ | j | j
        · have h1 := henv' tIO
          have hlo : l_6 tIO = min (l' tIO) (p' tIO + 1) := by simp [l_6, l_5, l_4]
          have hhi : u_6 tIO = max (u' tIO) (p' tIO + 1) := by simp [u_6, u_5, u_4]
          change L_env tIO ≤ l_6 tIO ∧ u_6 tIO ≤ U_env tIO
          rw [hlo, hhi, hpio']
          exact ⟨le_min h1.1 (by omega), max_le h1.2 (by omega)⟩
        · by_cases hj : j = A.inputTape
          · subst j; have h1 := henv' (tData A.inputTape)
            have hlo : l_6 (tData A.inputTape) = min (l' (tData A.inputTape)) (p' (tData A.inputTape) + 1) := by
              simp [l_6, l_5, l_4, p_4]
            have hhi : u_6 (tData A.inputTape) = max (u' (tData A.inputTape)) (p' (tData A.inputTape) + 1) := by
              simp [u_6, u_5, u_4, p_4]
            change L_env (tData A.inputTape) ≤ l_6 (tData A.inputTape) ∧ u_6 (tData A.inputTape) ≤ U_env (tData A.inputTape)
            rw [hlo, hhi, hpD']
            exact ⟨le_min h1.1 (by omega), max_le h1.2 (by omega)⟩
          · simp [l_6, u_6, l_5, u_5, l_4, u_4, hj, henv' (tData j)]
        · by_cases hj : j = A.inputTape
          · subst j; have h1 := henv' (tMark A.inputTape)
            have hlo : l_6 (tMark A.inputTape) = min (l' (tMark A.inputTape)) (p' (tMark A.inputTape) + 1) := by
              simp [l_6, l_5, l_4, p_5, p_4]
            have hhi : u_6 (tMark A.inputTape) = max (u' (tMark A.inputTape)) (p' (tMark A.inputTape) + 1) := by
              simp [u_6, u_5, u_4, p_5, p_4]
            change L_env (tMark A.inputTape) ≤ l_6 (tMark A.inputTape) ∧ u_6 (tMark A.inputTape) ≤ U_env (tMark A.inputTape)
            rw [hlo, hhi, hpM']
            exact ⟨le_min h1.1 (by omega), max_le h1.2 (by omega)⟩
          · simp [l_6, u_6, l_5, u_5, l_4, u_4, hj, henv' (tMark j)]
      have hpio6 : p_6 tIO = ((k + 1 : ℕ) : ℤ) := by
        simp [p_6, p_5, p_4, hpio']; try omega
      have hpD6 : p_6 (tData A.inputTape) = ((k + 1 : ℕ) : ℤ) := by
        simp [p_6, p_5, p_4, hpD']; try omega
      have hpM6 : p_6 (tMark A.inputTape) = ((k + 1 : ℕ) : ℤ) := by
        simp [p_6, p_5, p_4, hpM']; try omega
      have htio6 : IsWordAt (t_6 tIO) ((k + 1 : ℕ) : ℤ) input := by
        intro z
        have heq : t_6 tIO = (t' tIO).move .right := by
          dsimp [t_6, t_5, t_4, t_2, t_1]
          rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]
          by_cases hk0 : k = 0 <;> simp [hk0]
        rw [heq, show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by omega, absCell_move_right, htio']
      have htD6 : ∀ z : ℤ, absCell (t_6 (tData A.inputTape)) ((k + 1 : ℕ) : ℤ) z =
          if h : 0 ≤ z ∧ z.toNat < k + 1 then some input[z.toNat] else none := by
        intro z
        have heq : t_6 (tData A.inputTape) = ((t' (tData A.inputTape)).write (some b)).move .right := by
          dsimp [t_6, t_5, t_4, t_2, t_1]
          rw [Function.update_of_ne (by simp), Function.update_self, Function.update_of_ne (by simp)]
          by_cases hk0 : k = 0
          · simp [hk0]
          · simp [hk0]
        rw [heq, show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by omega, absCell_move_right, absCell_write]
        by_cases hz : z = k
        · subst z; simp [b]
        · rw [if_neg hz, htD' z]
          by_cases h1 : 0 ≤ z ∧ z.toNat < k
          · rw [dif_pos h1, dif_pos ⟨h1.1, by omega⟩]
          · rw [dif_neg h1, dif_neg (by intro h2; apply h1; exact ⟨h2.1, by omega⟩)]
      have htM6 : ∀ z : ℤ, absCell (t_6 (tMark A.inputTape)) ((k + 1 : ℕ) : ℤ) z =
          if z = 0 then some false else if 1 ≤ z ∧ z < ((k + 1 : ℕ) : ℤ) then some true else none := by
        intro z
        by_cases hk0 : k = 0
        · subst hk0
          have heq : t_6 (tMark A.inputTape) = (t' (tMark A.inputTape)).move .right := by
            dsimp [t_6, t_5, t_4, t_2, t_1]; simp
          rw [heq, show ((0 + 1 : ℕ) : ℤ) = (0 : ℤ) + 1 by omega, absCell_move_right,
            show absCell (t' (tMark A.inputTape)) 0 z = if z = 0 then some false else if 1 ≤ z ∧ z < ((0 : ℕ) : ℤ) then some true else none from by simpa [Int.natCast_zero] using htM' z]
          split_ifs <;> first | rfl | omega
        · have heq : t_6 (tMark A.inputTape) = ((t' (tMark A.inputTape)).write (some true)).move .right := by
            dsimp [t_6, t_5, t_4, t_2, t_1]; simp [hk0]
          rw [heq, show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by omega, absCell_move_right, absCell_write]
          by_cases hz : z = k
          · subst z; rw [if_pos rfl, if_neg (by omega), if_pos (by omega)]
          · rw [if_neg hz, htM' z]
            split_ifs <;> first | rfl | omega
      obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hout1, htio1, hp1io, hp1D, hp1M, hw1, henv1, hD1, hM1⟩ :=
        ih (k + 1) hlt (by omega) t_6 p_6 l_6 u_6 hw_6 henv_6 hpio6 hpD6 hpM6 htio6 htD6 htM6
      have hmid : Computation.Trace (locatedStep (resetMachine A outA)) (5 + if k = 0 then 1 else 2)
          (cCfg (rOps A outA) (rStart A) tIO (.inr qCopyInCheck) t' p' l' u')
          (cCfg (rOps A outA) (rStart A) tIO (.inr qCopyInCheck) t_6 p_6 l_6 u_6) := by
        have ha : Computation.Trace (locatedStep (resetMachine A outA)) 2
            (cCfg (rOps A outA) (rStart A) tIO (.inr qCopyInCheck) t' p' l' u')
            (cCfg (rOps A outA) (rStart A) tIO (.inr qCopyInCheckM) t_1 p' l' u') :=
          .cons hs0 (.cons hs1 (.refl _))
        have hb : Computation.Trace (locatedStep (resetMachine A outA)) 3
            (cCfg (rOps A outA) (rStart A) tIO (.inr qCopyInAdvIO) t_2 p' l' u')
            (cCfg (rOps A outA) (rStart A) tIO (.inr qCopyInCheck) t_6 p_6 l_6 u_6) :=
          .cons hs4 (.cons hs5 (.cons hs6 (.refl _)))
        have hab := Trace.append (Trace.append ha hM_branch) hb
        have hlen : 5 + (if k = 0 then 1 else 2) = (2 + (if k = 0 then 1 else 2)) + 3 := by
          split_ifs <;> omega
        rw [hlen]
        exact hab
      refine ⟨t1, p1, l1, u1, (5 + if k = 0 then 1 else 2) + n1, Trace.append hmid htail, ?_, ?_,
        htio1, hp1io, hp1D, hp1M, hw1, henv1, hD1, hM1⟩
      · split_ifs <;> omega
      · intro r' hr1 hr2 hr3
        have ho := hout1 r' hr1 hr2 hr3
        have hr4 : t_6 r' = t' r' ∧ p_6 r' = p' r' ∧ l_6 r' = l' r' ∧ u_6 r' = u' r' := by
          dsimp [t_6, t_5, t_4, t_2, t_1, p_6, p_5, p_4, l_6, l_5, l_4, u_6, u_5, u_4]
          by_cases hk0 : k = 0 <;> simp [hk0, hr1, hr2, hr3]
        exact ⟨ho.1.trans hr4.1, ho.2.1.trans hr4.2.1, ho.2.2.1.trans hr4.2.2.1, ho.2.2.2.trans hr4.2.2.2⟩
  refine ind input.length 0 (Nat.zero_le _) (Nat.sub_zero _) t p l u hw henv hpio hpD hpM htio ?_ ?_
  · intro z; simp only [htD, absCell, nth_mk₁_nil]; simp
  · intro z
    simp only [htM, absCell_write, Nat.cast_zero]
    by_cases hz : z = 0
    · subst hz; simp
    · rw [if_neg hz, if_neg hz, if_neg (by omega), absCell, sub_zero, nth_mk₁_nil]

private theorem rPhase_eraseIO (len : ℕ) (t : RCfg A) (p l u L_env U_env : RPos A)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r) (henv : ∀ r, L_env r ≤ l r ∧ u r ≤ U_env r)
    (hL : L_env tIO ≤ -1)
    (hp : p tIO = len)
    (ht : ∀ z : ℤ, absCell (t tIO) (len : ℤ) z = none ↔ ¬ (0 ≤ z ∧ z < (len : ℤ))) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (resetMachine A outA)) n
        (cCfg (rOps A outA) (rStart A) tIO (.inr qEraseIOStart) t p l u)
        (cCfg (rOps A outA) (rStart A) tIO (.inr qRewDStart) t1 p1 l1 u1) ∧
      n = 3 * len + 3 ∧
      (∀ r ≠ tIO, t1 r = t r ∧ p1 r = p r ∧ l1 r = l r ∧ u1 r = u r) ∧
      t1 tIO = Turing.Tape.mk₁ [] ∧ p1 tIO = 0 ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
  have loop : ∀ (k : ℕ) (t' : RCfg A) (p' l' u' : RPos A)
      (hw' : ∀ r, l' r ≤ p' r ∧ p' r ≤ u' r) (henv' : ∀ r, L_env r ≤ l' r ∧ u' r ≤ U_env r)
      (hp' : p' tIO = k)
      (ht' : ∀ z : ℤ, absCell (t' tIO) (k : ℤ) z = none ↔ ¬ (0 ≤ z ∧ z < (k : ℤ))),
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (resetMachine A outA)) n
          (cCfg (rOps A outA) (rStart A) tIO (.inr qEraseIOStart) t' p' l' u')
          (cCfg (rOps A outA) (rStart A) tIO (.inr qRewDStart) t1 p1 l1 u1) ∧
        n = 3 * k + 3 ∧
        (∀ r ≠ tIO, t1 r = t' r ∧ p1 r = p' r ∧ l1 r = l' r ∧ u1 r = u' r) ∧
        t1 tIO = Turing.Tape.mk₁ [] ∧ p1 tIO = 0 ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
    intro k
    induction k with
    | zero =>
      intro t' p' l' u' hw' henv' hp' ht'
      have hs0 := rStep_move_left A outA
        (q := qEraseIOStart) (q' := qEraseIOCheck) (k := tIO) rfl t' p' l' u'
      have hu1_eq : Function.update u' tIO (max (u' tIO) (p' tIO - 1)) = u' := by
        funext r; by_cases hr : r = tIO <;> simp [Function.update, hr]
        have := (hw' tIO).2; omega
      rw [hu1_eq] at hs0
      let t_1 := Function.update t' tIO ((t' tIO).move .left)
      let p_1 := Function.update p' tIO (p' tIO - 1)
      let l_1 := Function.update l' tIO (min (l' tIO) (p' tIO - 1))
      have hw1 : ∀ r, l_1 r ≤ p_1 r ∧ p_1 r ≤ u' r := by
        intro r; by_cases hr : r = tIO
        · subst r; simp only [p_1, l_1, Function.update_self]
          exact ⟨min_le_right _ _, by have := (hw' tIO).2; omega⟩
        · simp [p_1, l_1, hr, hw' r]
      have hhead : (t_1 tIO).head = none := by
        have hs : (t_1 tIO).head = absCell ((t' tIO).move .left) (p' tIO - 1) (p' tIO - 1) := by
          simp [t_1, absCell_self]
        rw [hs, absCell_move_left, hp', ht']
        omega
      have hs1 := rStep_branch A outA
        (q := qEraseIOCheck) (k := tIO) rfl t_1 p_1 l_1 u' (hw1 tIO)
      rw [hhead] at hs1
      have hs2 := rStep_move_right A outA
        (q := qEraseIORight) (q' := qRewDStart) (k := tIO) rfl t_1 p_1 l_1 u'
      let t_2 := Function.update t_1 tIO ((t_1 tIO).move .right)
      let p_2 := Function.update p_1 tIO (p_1 tIO + 1)
      let l_2 := Function.update l_1 tIO (min (l_1 tIO) (p_1 tIO + 1))
      let u_2 := Function.update u' tIO (max (u' tIO) (p_1 tIO + 1))
      have ht_eq : t_2 tIO = Turing.Tape.mk₁ [] := by
        apply (blank_iff_absCell (p := (0 : ℤ))).1
        intro z
        have heq : t_2 tIO = t' tIO := by simp [t_2, t_1]
        rw [heq, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, ht']; omega
      have hp_eq : p_2 tIO = 0 := by simp [p_2, p_1, hp']
      have hw2 : ∀ r, l_2 r ≤ p_2 r ∧ p_2 r ≤ u_2 r := by
        intro r; by_cases hr : r = tIO
        · subst r; simp only [p_2, l_2, u_2, Function.update_self]
          exact ⟨min_le_right _ _, le_max_right _ _⟩
        · simp only [p_2, p_1, l_2, l_1, u_2, Function.update_of_ne hr]; exact hw' r
      have henv2 : ∀ r, L_env r ≤ l_2 r ∧ u_2 r ≤ U_env r := by
        intro r; by_cases hr : r = tIO
        · subst r; have h1 := henv' tIO; have h2 := hw' tIO
          have hlo : l_2 tIO = min (min (l' tIO) (p' tIO - 1)) (p' tIO - 1 + 1) := by
            simp [l_2, l_1, p_1]
          have hhi : u_2 tIO = max (u' tIO) (p' tIO - 1 + 1) := by simp [u_2, p_1]
          rw [hlo, hhi, hp']
          exact ⟨le_min (le_min h1.1 (by omega)) (by omega), max_le h1.2 (by omega)⟩
        · simp [l_2, u_2, l_1, hr, henv' r]
      exact ⟨t_2, p_2, l_2, u_2, 3, .cons hs0 (.cons hs1 (.cons hs2 (.refl _))), rfl,
        fun r hr => by simp [t_2, t_1, p_2, p_1, l_2, l_1, u_2, hr], ht_eq, hp_eq, hw2, henv2⟩
    | succ k ih =>
      intro t' p' l' u' hw' henv' hp' ht'
      have hs0 := rStep_move_left A outA
        (q := qEraseIOStart) (q' := qEraseIOCheck) (k := tIO) rfl t' p' l' u'
      have hu1_eq : Function.update u' tIO (max (u' tIO) (p' tIO - 1)) = u' := by
        funext r; by_cases hr : r = tIO <;> simp [Function.update, hr]
        have := (hw' tIO).2; omega
      rw [hu1_eq] at hs0
      let t_1 := Function.update t' tIO ((t' tIO).move .left)
      let p_1 := Function.update p' tIO (p' tIO - 1)
      let l_1 := Function.update l' tIO (min (l' tIO) (p' tIO - 1))
      have hw1 : ∀ r, l_1 r ≤ p_1 r ∧ p_1 r ≤ u' r := by
        intro r; by_cases hr : r = tIO
        · subst r; simp only [p_1, l_1, Function.update_self]
          exact ⟨min_le_right _ _, by have := (hw' tIO).2; omega⟩
        · simp [p_1, l_1, hr, hw' r]
      have hne : (t_1 tIO).head ≠ none := by
        have hs : (t_1 tIO).head = absCell ((t' tIO).move .left) (p' tIO - 1) (p' tIO - 1) := by
          simp [t_1, absCell_self]
        intro hbad
        rw [hs, absCell_move_left, hp', ht'] at hbad
        omega
      rcases Option.ne_none_iff_exists'.1 hne with ⟨b, hhead⟩
      have hs1 := rStep_branch A outA
        (q := qEraseIOCheck) (k := tIO) rfl t_1 p_1 l_1 u' (hw1 tIO)
      rw [hhead] at hs1
      have hs2 := rStep_write A outA
        (q := qEraseIOWrite) (q' := qEraseIOStart) (k := tIO) (sym := none) rfl
        t_1 p_1 l_1 u' (hw1 tIO)
      let t_2 := Function.update t_1 tIO ((t_1 tIO).write none)
      have hp2 : p_1 tIO = k := by simp [p_1, hp']; try omega
      have ht2 : ∀ z : ℤ, absCell (t_2 tIO) (k : ℤ) z = none ↔ ¬ (0 ≤ z ∧ z < (k : ℤ)) := by
        intro z
        have heq : t_2 tIO = ((t' tIO).move .left).write none := by simp [t_2, t_1]
        rw [heq, show (k : ℤ) = ((k + 1 : ℕ) : ℤ) - 1 by omega, absCell_write, absCell_move_left]
        by_cases hz : z = ((k + 1 : ℕ) : ℤ) - 1
        · subst z; simp
        · rw [if_neg hz, ht' z]; omega
      have henv1 : ∀ r, L_env r ≤ l_1 r ∧ u' r ≤ U_env r := by
        intro r; by_cases hr : r = tIO
        · subst r; have h1 := henv' tIO; have h2 := hw' tIO
          have hlo : l_1 tIO = min (l' tIO) (p' tIO - 1) := by simp [l_1]
          rw [hlo, hp']
          exact ⟨le_min h1.1 (by omega), h1.2⟩
        · simp [l_1, hr, henv' r]
      obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hout1, ht_eq, hp_eq, hw2, henv2⟩ :=
        ih t_2 p_1 l_1 u' hw1 henv1 hp2 ht2
      refine ⟨t1, p1, l1, u1, 3 + n1, trace_prepend3 hs0 hs1 hs2 htail,
        by omega, ?_, ht_eq, hp_eq, hw2, henv2⟩
      intro r hr
      have ho := hout1 r hr
      have hr' : t_2 r = t' r ∧ p_1 r = p' r ∧ l_1 r = l' r := by simp [t_2, t_1, p_1, l_1, hr]
      exact ⟨ho.1.trans hr'.1, ho.2.1.trans hr'.2.1, ho.2.2.1.trans hr'.2.2, ho.2.2.2⟩
  exact loop len t p l u hw henv hp ht

private theorem rPhase_rewindLeft (qStart qCheck qRight qNext : RQ A.tapeCount A.stateCount)
    (k : RTape A.tapeCount) (len : ℕ)
    (h1 : rOps A outA qStart = .act k (.move .left) qCheck)
    (h2 : rOps A outA qCheck = .branch k fun | none => qRight | some _ => qStart)
    (h3 : rOps A outA qRight = .act k (.move .right) qNext)
    (t : RCfg A) (p l u L_env U_env : RPos A)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r) (henv : ∀ r, L_env r ≤ l r ∧ u r ≤ U_env r)
    (hLk : L_env k ≤ -1) (hp : p k = len)
    (ht_neg1 : absCell (t k) (len : ℤ) (-1) = none)
    (ht_nonneg : ∀ z : ℤ, 0 ≤ z → z < (len : ℤ) → absCell (t k) (len : ℤ) z ≠ none) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (resetMachine A outA)) n
        (cCfg (rOps A outA) (rStart A) tIO (.inr qStart) t p l u)
        (cCfg (rOps A outA) (rStart A) tIO (.inr qNext) t1 p1 l1 u1) ∧
      n = 2 * len + 3 ∧
      (∀ r ≠ k, t1 r = t r ∧ p1 r = p r ∧ l1 r = l r ∧ u1 r = u r) ∧
      (∀ z : ℤ, absCell (t1 k) 0 z = absCell (t k) (len : ℤ) z) ∧
      p1 k = 0 ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
  let tk0 := t k
  have loop2 : ∀ (m : ℕ) (_hm : m ≤ len) (t' : RCfg A) (p' l' u' : RPos A)
      (hw' : ∀ r, l' r ≤ p' r ∧ p' r ≤ u' r) (henv' : ∀ r, L_env r ≤ l' r ∧ u' r ≤ U_env r)
      (hp' : p' k = m)
      (ht_rel : ∀ z : ℤ, absCell (t' k) (m : ℤ) z = absCell tk0 (len : ℤ) z),
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (resetMachine A outA)) n
          (cCfg (rOps A outA) (rStart A) tIO (.inr qStart) t' p' l' u')
          (cCfg (rOps A outA) (rStart A) tIO (.inr qNext) t1 p1 l1 u1) ∧
        n = 2 * m + 3 ∧
        (∀ r ≠ k, t1 r = t' r ∧ p1 r = p' r ∧ l1 r = l' r ∧ u1 r = u' r) ∧
        (∀ z : ℤ, absCell (t1 k) 0 z = absCell tk0 (len : ℤ) z) ∧
        p1 k = 0 ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
    intro m
    induction m with
    | zero =>
      intro _ t' p' l' u' hw' henv' hp' ht_rel
      have hs0 := rStep_move_left A outA
        (q := qStart) (q' := qCheck) (k := k) h1 t' p' l' u'
      have hu1_eq : Function.update u' k (max (u' k) (p' k - 1)) = u' := by
        funext r; by_cases hr : r = k <;> simp [Function.update, hr]
        have := (hw' k).2; omega
      rw [hu1_eq] at hs0
      let t_1 := Function.update t' k ((t' k).move .left)
      let p_1 := Function.update p' k (p' k - 1)
      let l_1 := Function.update l' k (min (l' k) (p' k - 1))
      have hw1 : ∀ r, l_1 r ≤ p_1 r ∧ p_1 r ≤ u' r := by
        intro r; by_cases hr : r = k
        · subst r; simp only [p_1, l_1, Function.update_self]
          exact ⟨min_le_right _ _, by have := (hw' k).2; omega⟩
        · simp [p_1, l_1, hr, hw' r]
      have hhead : (t_1 k).head = none := by
        have hstep : (t_1 k).head = absCell ((t' k).move .left) (p' k - 1) (p' k - 1) := by
          simp [t_1, absCell_self]
        rw [hstep, absCell_move_left, hp', ht_rel, show ((0 : ℕ) : ℤ) - 1 = (-1 : ℤ) by omega, ht_neg1]
      have hs1 := rStep_branch A outA
        (q := qCheck) (k := k) h2 t_1 p_1 l_1 u' (hw1 k)
      rw [hhead] at hs1
      have hs2 := rStep_move_right A outA
        (q := qRight) (q' := qNext) (k := k) h3 t_1 p_1 l_1 u'
      let t_2 := Function.update t_1 k ((t_1 k).move .right)
      let p_2 := Function.update p_1 k (p_1 k + 1)
      let l_2 := Function.update l_1 k (min (l_1 k) (p_1 k + 1))
      let u_2 := Function.update u' k (max (u' k) (p_1 k + 1))
      have ht_eq : ∀ z : ℤ, absCell (t_2 k) 0 z = absCell tk0 (len : ℤ) z := by
        intro z
        have heq : t_2 k = t' k := by simp [t_2, t_1]
        rw [heq]; exact ht_rel z
      have hp_eq : p_2 k = 0 := by simp [p_2, p_1, hp']
      have hw2 : ∀ r, l_2 r ≤ p_2 r ∧ p_2 r ≤ u_2 r := by
        intro r; by_cases hr : r = k
        · subst r; simp only [p_2, l_2, u_2, Function.update_self]
          exact ⟨min_le_right _ _, le_max_right _ _⟩
        · simp only [p_2, p_1, l_2, l_1, u_2, Function.update_of_ne hr]; exact hw' r
      have henv2 : ∀ r, L_env r ≤ l_2 r ∧ u_2 r ≤ U_env r := by
        intro r; by_cases hr : r = k
        · subst r; have h1 := henv' k; have h2 := hw' k
          have hlo : l_2 k = min (min (l' k) (p' k - 1)) (p' k - 1 + 1) := by simp [l_2, l_1, p_1]
          have hhi : u_2 k = max (u' k) (p' k - 1 + 1) := by simp [u_2, p_1]
          rw [hlo, hhi, hp']
          exact ⟨le_min (le_min h1.1 (by omega)) (by omega), max_le h1.2 (by omega)⟩
        · simp [l_2, u_2, l_1, hr, henv' r]
      exact ⟨t_2, p_2, l_2, u_2, 3, .cons hs0 (.cons hs1 (.cons hs2 (.refl _))), rfl,
        fun r hr => by simp [t_2, t_1, p_2, p_1, l_2, l_1, u_2, hr], ht_eq, hp_eq, hw2, henv2⟩
    | succ m ih =>
      intro hm t' p' l' u' hw' henv' hp' ht_rel
      have hs0 := rStep_move_left A outA
        (q := qStart) (q' := qCheck) (k := k) h1 t' p' l' u'
      have hu1_eq : Function.update u' k (max (u' k) (p' k - 1)) = u' := by
        funext r; by_cases hr : r = k <;> simp [Function.update, hr]
        have := (hw' k).2; omega
      rw [hu1_eq] at hs0
      let t_1 := Function.update t' k ((t' k).move .left)
      let p_1 := Function.update p' k (p' k - 1)
      let l_1 := Function.update l' k (min (l' k) (p' k - 1))
      have hw1 : ∀ r, l_1 r ≤ p_1 r ∧ p_1 r ≤ u' r := by
        intro r; by_cases hr : r = k
        · subst r; simp only [p_1, l_1, Function.update_self]
          exact ⟨min_le_right _ _, by have := (hw' k).2; omega⟩
        · simp [p_1, l_1, hr, hw' r]
      have hne : (t_1 k).head ≠ none := by
        have hstep : (t_1 k).head = absCell ((t' k).move .left) (p' k - 1) (p' k - 1) := by
          simp [t_1, absCell_self]
        intro hbad
        rw [hstep, absCell_move_left, hp', ht_rel] at hbad
        exact ht_nonneg (m : ℤ) (Int.natCast_nonneg m) (by omega)
          (by simpa [show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) by omega] using hbad)
      rcases Option.ne_none_iff_exists'.1 hne with ⟨b, hhead⟩
      have hs1 := rStep_branch A outA
        (q := qCheck) (k := k) h2 t_1 p_1 l_1 u' (hw1 k)
      rw [hhead] at hs1
      have hp1 : p_1 k = m := by simp [p_1, hp']; try omega
      have hrel1 : ∀ z : ℤ, absCell (t_1 k) (m : ℤ) z = absCell tk0 (len : ℤ) z := by
        intro z
        have heq : t_1 k = (t' k).move .left := by simp [t_1]
        rw [heq, show (m : ℤ) = ((m + 1 : ℕ) : ℤ) - 1 by omega, absCell_move_left]
        exact ht_rel z
      have henv1 : ∀ r, L_env r ≤ l_1 r ∧ u' r ≤ U_env r := by
        intro r; by_cases hr : r = k
        · subst r; have h1 := henv' k; simp only [l_1, Function.update_self, hp']
          exact ⟨le_min h1.1 (by omega), h1.2⟩
        · simp [l_1, hr, henv' r]
      obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hout1, htz, hp1z, hw2, henv2⟩ :=
        ih (by omega) t_1 p_1 l_1 u' hw1 henv1 hp1 hrel1
      refine ⟨t1, p1, l1, u1, 2 + n1, trace_prepend2 hs0 hs1 htail,
        by omega, ?_, htz, hp1z, hw2, henv2⟩
      intro r hr
      have ho := hout1 r hr
      have hr' : t_1 r = t' r ∧ p_1 r = p' r ∧ l_1 r = l' r := by simp [t_1, p_1, l_1, hr]
      exact ⟨ho.1.trans hr'.1, ho.2.1.trans hr'.2.1, ho.2.2.1.trans hr'.2.2, ho.2.2.2⟩
  exact loop2 len le_rfl t p l u hw henv hp (fun _ => rfl)

private theorem rPhase_sim (steps : ℕ) {cA dA : LocatedCfg A}
    (htr : Computation.Trace (locatedStep A) steps cA dA)
    (bAns : Bool) (hdA : dA.config.state = .inl bAns) :
    ∀ {qA : Fin A.stateCount} (t : RCfg A) (p l u L_env U_env : RPos A),
      cA.config.state = .inr qA →
      (∀ r, l r ≤ p r ∧ p r ≤ u r) →
      (∀ r, L_env r ≤ l r ∧ u r ≤ U_env r) →
      LocatedWellFormed cA →
      TapeSupportBound cA →
      (∀ j, t (tData j) = cA.config.tapes j ∧ p (tData j) = cA.position j) →
      (∀ j, p (tMark j) = cA.position j ∧ MarkExact (t (tMark j)) (p (tMark j)) (cA.lower j) (cA.upper j)) →
      (∀ j, L_env (tData j) ≤ dA.lower j ∧ dA.upper j ≤ U_env (tData j) ∧
            L_env (tMark j) ≤ dA.lower j ∧ dA.upper j ≤ U_env (tMark j)) →
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (resetMachine A outA)) n
          (cCfg (rOps A outA) (rStart A) tIO (.inr (qSim qA)) t p l u)
          (cCfg (rOps A outA) (rStart A) tIO (.inr qOutRead) t1 p1 l1 u1) ∧
        n ≤ 4 * steps ∧
        t1 tIO = t tIO ∧ p1 tIO = p tIO ∧ l1 tIO = l tIO ∧ u1 tIO = u tIO ∧
        (∀ j, t1 (tData j) = dA.config.tapes j ∧ p1 (tData j) = dA.position j) ∧
        (∀ j, p1 (tMark j) = dA.position j ∧ MarkExact (t1 (tMark j)) (p1 (tMark j)) (dA.lower j) (dA.upper j)) ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
  induction steps generalizing cA with
  | zero =>
    intro qA t p l u L_env U_env hcA _ _ _ _ _ _ _
    have heq := (Trace.zero_iff).1 htr
    subst heq; rw [hcA] at hdA; cases hdA
  | succ m ih =>
    intro qA t p l u L_env U_env hcA hw henv hwA hsup hD hM hbd
    cases htr with
    | @cons _ _ bA _ hsA hrest =>
      unfold locatedStep at hsA
      cases hcstep : A.step cA.config with
      | none => simp [hcstep] at hsA
      | some cfgA' =>
        have hmidA : cA.monitor cfgA' = bA := by simpa [hcstep] using hsA
        rcases cA with ⟨⟨stA, tapesA⟩, posA, lowA, uppA⟩
        dsimp at hcA; subst hcA
        let j := A.scan qA
        have hhdD : (t (tData j)).head = (tapesA j).head := (hD j).1 ▸ rfl
        cases htrA : A.transition qA (tapesA j).head with
        | inl b =>
          dsimp only [j] at htrA
          have hmid_eq : cfgA' = ⟨.inl b, tapesA⟩ := by
            simp only [PrimitiveMachine.step, htrA, Option.some.injEq] at hcstep
            exact hcstep.symm
          subst hmid_eq
          have hnil : m = 0 := by
            cases hrest with
            | refl => rfl
            | cons hdead _ =>
              exfalso; rw [← hmidA] at hdead
              simp [locatedStep, PrimitiveMachine.step, LocatedCfg.monitor, htrA] at hdead
          subst hnil
          have hd_eq : (⟨⟨.inl b, tapesA⟩, posA, lowA, uppA⟩ : LocatedCfg A) = dA := by
            have hz := (Trace.zero_iff).1 hrest
            rw [← hmidA] at hz
            simpa [LocatedCfg.monitor, htrA] using hz
          have hstep1 := rStep_raw_write A outA
            (q := qSim qA) (q' := qOutRead) (k := tData j) (sym := (t (tData j)).head)
            rfl t p l u (by simp [j, hhdD, htrA]) (hw (tData j))
          have hwr : Function.update t (tData j) ((t (tData j)).write (t (tData j)).head) = t := by
            rw [Turing.Tape.write_self, Function.update_eq_self]
          rw [hwr] at hstep1
          refine ⟨t, p, l, u, 1, .cons hstep1 (.refl _), by omega, rfl, rfl, rfl, rfl,
            ?_, ?_, hw, henv⟩
          · intro i; rw [← hd_eq]; exact hD i
          · intro i; rw [← hd_eq]; exact hM i
        | inr qa =>
          dsimp only [j] at htrA
          rcases qa with ⟨qA', act⟩
          let cA1 := (⟨⟨.inr qA, tapesA⟩, posA, lowA, uppA⟩ : LocatedCfg A).monitor cfgA'
          have hcA1_eq : cA1 = bA := hmidA
          have hrest' : Computation.Trace (locatedStep A) m cA1 dA := hcA1_eq.symm ▸ hrest
          have hwA1 : LocatedWellFormed cA1 := hcA1_eq.symm ▸ locatedWellFormed_step hwA hsA
          have hsup1 : TapeSupportBound cA1 := hcA1_eq.symm ▸ tapeSupportBound_step hwA hsup hsA
          have hcA1_st : cA1.config.state = .inr qA' := by
            cases act with
            | write w =>
              have hmid_cfg : cfgA' = ⟨.inr qA', Function.update tapesA (A.scan qA) ((tapesA (A.scan qA)).write w)⟩ := by
                simp only [PrimitiveMachine.step, htrA, Option.some.injEq] at hcstep; exact hcstep.symm
              simp [cA1, LocatedCfg.monitor, htrA, hmid_cfg]
            | move dir =>
              have hmid_cfg : cfgA' = ⟨.inr qA', Function.update tapesA (A.scan qA) ((tapesA (A.scan qA)).move dir)⟩ := by
                simp only [PrimitiveMachine.step, htrA, Option.some.injEq] at hcstep; exact hcstep.symm
              simp [cA1, LocatedCfg.monitor, htrA, hmid_cfg]
          have hbd1 : ∀ i, L_env (tData i) ≤ dA.lower i ∧ dA.upper i ≤ U_env (tData i) ∧
              L_env (tMark i) ≤ dA.lower i ∧ dA.upper i ≤ U_env (tMark i) := hbd
          cases act with
          | write w =>
            have hstep1 := rStep_raw_write A outA
              (q := qSim qA) (q' := qSim qA') (k := tData j) (sym := w)
              rfl t p l u (by simp [j, hhdD, htrA]) (hw (tData j))
            let t_1 := Function.update t (tData j) ((t (tData j)).write w)
            have hD1 : ∀ i, t_1 (tData i) = cA1.config.tapes i ∧ p (tData i) = cA1.position i := by
              intro i
              have hmid_cfg : cfgA' = ⟨.inr qA', Function.update tapesA (A.scan qA) ((tapesA (A.scan qA)).write w)⟩ := by
                simp only [PrimitiveMachine.step, htrA, Option.some.injEq] at hcstep
                exact hcstep.symm
              by_cases hi : i = j
              · subst i; simp [t_1, j, cA1, LocatedCfg.monitor, htrA, hmid_cfg, headDisplacement, (hD (A.scan qA)).1, (hD (A.scan qA)).2]
              · simp [t_1, j, cA1, LocatedCfg.monitor, htrA, hmid_cfg, hi, hD i]
            have hM1 : ∀ i, p (tMark i) = cA1.position i ∧
                MarkExact (t_1 (tMark i)) (p (tMark i)) (cA1.lower i) (cA1.upper i) := by
              intro i
              have hne : (tMark i : RTape A.tapeCount) ≠ tData j := by simp
              rw [show t_1 (tMark i) = t (tMark i) from Function.update_of_ne hne _ _]
              by_cases hi : i = j
              · subst i
                have hwj := hwA j
                have hl_eq : cA1.lower j = lowA j := by
                  simp [cA1, LocatedCfg.monitor, htrA, j, headDisplacement, min_eq_left hwj.1]
                have hu_eq : cA1.upper j = uppA j := by
                  simp [cA1, LocatedCfg.monitor, htrA, j, headDisplacement, max_eq_left hwj.2]
                have hp_eq : cA1.position j = posA j := by
                  simp [cA1, LocatedCfg.monitor, htrA, j, headDisplacement]
                rw [hp_eq, hl_eq, hu_eq]; exact hM j
              · have hm_eq : cA1.position i = posA i ∧ cA1.lower i = lowA i ∧ cA1.upper i = uppA i := by
                  simp [cA1, LocatedCfg.monitor, htrA, j, hi]
                rw [hm_eq.1, hm_eq.2.1, hm_eq.2.2]; exact hM i
            obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hio, hpio, hlio, huio, hDf, hMf, hw_f, henv_f⟩ :=
              ih hrest' t_1 p l u L_env U_env hcA1_st hw henv hwA1 hsup1 hD1 hM1 hbd1
            exact ⟨t1, p1, l1, u1, 1 + n1, trace_prepend1 hstep1 htail, by omega, hio, hpio, hlio, huio,
              hDf, hMf, hw_f, henv_f⟩
          | move dir =>
            have hstep1 := rStep_raw_move A outA
              (q := qSim qA) (q' := qSimMoveM j qA' dir) (k := tData j) (dir := dir)
              rfl t p l u (by simp [j, hhdD, htrA])
            let pos1 := p (tData j) + headDisplacement (.move dir)
            let t_1 := Function.update t (tData j) ((t (tData j)).move dir)
            let p_1 := Function.update p (tData j) pos1
            let l_1 := Function.update l (tData j) (min (l (tData j)) pos1)
            let u_1 := Function.update u (tData j) (max (u (tData j)) pos1)
            have hstep2 := rStep_move A outA
              (q := qSimMoveM j qA' dir) (q' := qSimCheckM j qA') (k := tMark j) (dir := dir)
              (rOps_simMoveM A outA j qA' dir) t_1 p_1 l_1 u_1
            let pos1M := p_1 (tMark j) + headDisplacement (.move dir)
            let t_2 := Function.update t_1 (tMark j) ((t_1 (tMark j)).move dir)
            let p_2 := Function.update p_1 (tMark j) pos1M
            let l_2 := Function.update l_1 (tMark j) (min (l_1 (tMark j)) pos1M)
            let u_2 := Function.update u_1 (tMark j) (max (u_1 (tMark j)) pos1M)
            have hpos_eq1 : pos1 = cA1.position j := by
              simp [pos1, cA1, LocatedCfg.monitor, htrA, j, (hD (A.scan qA)).2]
            have hpos_eq2 : pos1M = cA1.position j := by
              simp [pos1M, p_1, cA1, LocatedCfg.monitor, htrA, j, (hM (A.scan qA)).1]
            have hw2 : ∀ r, l_2 r ≤ p_2 r ∧ p_2 r ≤ u_2 r := by
              intro r
              rcases r with _ | i | i
              · simpa [p_2, p_1, l_2, l_1, u_2, u_1] using hw tIO
              · by_cases hi : i = j
                · subst i; simp [p_2, p_1, l_2, l_1, u_2, u_1]
                · simp [p_2, p_1, l_2, l_1, u_2, u_1, hi, hw]
              · by_cases hi : i = j
                · subst i; simp [p_2, p_1, l_2, l_1, u_2, u_1]
                · simp [p_2, p_1, l_2, l_1, u_2, u_1, hi, hw]
            have henv2 : ∀ r, L_env r ≤ l_2 r ∧ u_2 r ≤ U_env r := by
              intro r
              have hexp := locatedTrace_expands hrest' j
              have hlow_d : dA.lower j ≤ pos1 := by
                have hcA1l : cA1.lower j = min (lowA j) pos1 := by
                  simp [cA1, LocatedCfg.monitor, htrA, j, pos1, (hD (A.scan qA)).2]
                exact hexp.1.trans (hcA1l ▸ min_le_right _ _)
              have hupp_d : pos1 ≤ dA.upper j := by
                have hcA1u : cA1.upper j = max (uppA j) pos1 := by
                  simp [cA1, LocatedCfg.monitor, htrA, j, pos1, (hD (A.scan qA)).2]
                exact (le_max_right _ _).trans (hcA1u ▸ hexp.2)
              have hbdj := hbd j
              rcases r with _ | i | i
              · simpa [l_2, l_1, u_2, u_1] using henv tIO
              · by_cases hi : i = j
                · subst i; have h1 := henv (tData j)
                  change L_env (tData j) ≤ l_2 (tData j) ∧ u_2 (tData j) ≤ U_env (tData j)
                  have hlo : l_2 (tData j) = min (l (tData j)) pos1 := by simp [l_2, l_1]
                  have hhi : u_2 (tData j) = max (u (tData j)) pos1 := by simp [u_2, u_1]
                  rw [hlo, hhi]
                  exact ⟨le_min h1.1 (by omega), max_le h1.2 (by omega)⟩
                · simp [l_2, l_1, u_2, u_1, hi, henv]
              · by_cases hi : i = j
                · subst i; have h1 := henv (tMark j)
                  change L_env (tMark j) ≤ l_2 (tMark j) ∧ u_2 (tMark j) ≤ U_env (tMark j)
                  have hlo : l_2 (tMark j) = min (l (tMark j)) pos1M := by simp [l_2, l_1]
                  have hhi : u_2 (tMark j) = max (u (tMark j)) pos1M := by simp [u_2, u_1]
                  rw [hlo, hhi, hpos_eq2, ← hpos_eq1]
                  exact ⟨le_min h1.1 (by omega), max_le h1.2 (by omega)⟩
                · simp [l_2, l_1, u_2, u_1, hi, henv]
            have hstep3 := rStep_branch A outA
              (q := qSimCheckM j qA') (k := tMark j) rfl t_2 p_2 l_2 u_2 (hw2 (tMark j))
            have hM_pre := (hM j).2
            have ht2M_cell : ∀ z : ℤ, absCell (t_2 (tMark j)) pos1M z =
                if z = 0 then some false else if lowA j ≤ z ∧ z ≤ uppA j then some true else none := by
              intro z
              have heq : t_2 (tMark j) = (t (tMark j)).move dir := by simp [t_2, t_1]
              have hpM_eq : pos1M = p (tMark j) + headDisplacement (.move dir) := by simp [pos1M, p_1]
              rw [heq, hpM_eq]
              cases dir with
              | left =>
                simp only [headDisplacement]
                rw [show p (tMark j) + (-1 : ℤ) = p (tMark j) - 1 by omega, absCell_move_left]
                exact hM_pre.2.2.2.2 z
              | right =>
                simp only [headDisplacement, absCell_move_right]
                exact hM_pre.2.2.2.2 z
            have hheadM2 : (t_2 (tMark j)).head =
                if pos1M = 0 then some false else if lowA j ≤ pos1M ∧ pos1M ≤ uppA j then some true else none := by
              rw [← absCell_self (t_2 (tMark j)) (p_2 (tMark j))]
              have hp2M : p_2 (tMark j) = pos1M := by simp [p_2]
              rw [hp2M]; exact ht2M_cell pos1M
            have hbranch : ∃ t_3 nB,
                Computation.Trace (locatedStep (resetMachine A outA)) nB
                  (cCfg (rOps A outA) (rStart A) tIO (.inr (qSimCheckM j qA')) t_2 p_2 l_2 u_2)
                  (cCfg (rOps A outA) (rStart A) tIO (.inr (qSim qA')) t_3 p_2 l_2 u_2) ∧
                nB ≤ 2 ∧
                (∀ r ≠ tMark j, t_3 r = t_2 r) ∧
                MarkExact (t_3 (tMark j)) pos1M (cA1.lower j) (cA1.upper j) := by
              have hcA1_low : cA1.lower j = min (lowA j) pos1M := by
                simp [cA1, LocatedCfg.monitor, htrA, j, pos1M, p_1, (hM (A.scan qA)).1]
              have hcA1_upp : cA1.upper j = max (uppA j) pos1M := by
                simp [cA1, LocatedCfg.monitor, htrA, j, pos1M, p_1, (hM (A.scan qA)).1]
              have hdisp1 : pos1M = posA j - 1 ∨ pos1M = posA j + 1 := by
                have hmj := (hM j).1
                cases dir with
                | left => left; dsimp [pos1M, p_1]; rw [Function.update_of_ne (by simp), hmj]; simp [headDisplacement]; try omega
                | right => right; dsimp [pos1M, p_1]; rw [Function.update_of_ne (by simp), hmj]; simp [headDisplacement]; try omega
              have hposA_lu := hwA j
              by_cases hin : lowA j ≤ pos1M ∧ pos1M ≤ uppA j
              · have hl_eq : cA1.lower j = lowA j := by rw [hcA1_low]; exact min_eq_left hin.1
                have hu_eq : cA1.upper j = uppA j := by rw [hcA1_upp]; exact max_eq_left hin.2
                have hne : (t_2 (tMark j)).head ≠ none := by rw [hheadM2]; split_ifs <;> simp
                rcases Option.ne_none_iff_exists'.1 hne with ⟨symM, hsM⟩
                rw [hsM] at hstep3
                refine ⟨t_2, 1, .cons hstep3 (.refl _), by omega, fun _ _ => rfl, ?_⟩
                rw [hl_eq, hu_eq]
                exact ⟨hM_pre.1, hM_pre.2.1, hin.1, hin.2, ht2M_cell⟩
              · have hne0 : pos1M ≠ 0 := fun h0 => hin ⟨h0 ▸ hM_pre.1, h0 ▸ hM_pre.2.1⟩
                have hhead_none : (t_2 (tMark j)).head = none := by rw [hheadM2, if_neg hne0, if_neg hin]
                rw [hhead_none] at hstep3
                have hstep4 := rStep_write A outA
                  (q := qSimWriteM j qA') (q' := qSim qA') (k := tMark j) (sym := some true) rfl
                  t_2 p_2 l_2 u_2 (hw2 (tMark j))
                refine ⟨Function.update t_2 (tMark j) ((t_2 (tMark j)).write (some true)), 2,
                  .cons hstep3 (.cons hstep4 (.refl _)), le_rfl, fun r hr => Function.update_of_ne hr _ _, ?_⟩
                refine ⟨by rw [hcA1_low]; exact min_le_of_left_le hM_pre.1,
                        by rw [hcA1_upp]; exact le_max_of_le_left hM_pre.2.1,
                        by rw [hcA1_low]; exact min_le_right _ _,
                        by rw [hcA1_upp]; exact le_max_right _ _, ?_⟩
                intro z
                rw [Function.update_self, absCell_write, ht2M_cell z]
                have hadj : (z = pos1M ∨ (lowA j ≤ z ∧ z ≤ uppA j)) ↔ (cA1.lower j ≤ z ∧ z ≤ cA1.upper j) := by
                  rw [hcA1_low, hcA1_upp]
                  dsimp only at hposA_lu
                  have hlo : lowA j ≤ posA j := hposA_lu.1
                  have hhi : posA j ≤ uppA j := hposA_lu.2
                  rcases hdisp1 with h1 | h1 <;> omega
                by_cases hz : z = pos1M
                · subst z; rw [if_pos rfl, if_neg hne0,
                    if_pos (by rw [hcA1_low, hcA1_upp]; exact ⟨min_le_right _ _, le_max_right _ _⟩)]
                · rw [if_neg hz]
                  by_cases hz0 : z = 0
                  · simp [hz0]
                  · rw [if_neg hz0, if_neg hz0]
                    by_cases h1 : lowA j ≤ z ∧ z ≤ uppA j
                    · rw [if_pos h1, if_pos (hadj.mp (.inr h1))]
                    · rw [if_neg h1, if_neg (fun h2 => h1 (by rcases hadj.mpr h2 with rfl | h'; exact (hz rfl).elim; exact h'))]
            obtain ⟨t_3, nB, htrB, hnB, htr3_out, hM3_exact⟩ := hbranch
            have hD3 : ∀ i, t_3 (tData i) = cA1.config.tapes i ∧ p_2 (tData i) = cA1.position i := by
              intro i
              rw [htr3_out (tData i) (by simp)]
              have hmid_cfg : cfgA' = ⟨.inr qA', Function.update tapesA (A.scan qA) ((tapesA (A.scan qA)).move dir)⟩ := by
                simp only [PrimitiveMachine.step, htrA, Option.some.injEq] at hcstep
                exact hcstep.symm
              by_cases hi : i = j
              · subst i
                have ht2D : t_2 (tData j) = (t (tData j)).move dir := by simp [t_2, t_1]
                have hp2D : p_2 (tData j) = pos1 := by simp [p_2, p_1]
                rw [ht2D, hp2D, hpos_eq1]
                simp [j, cA1, LocatedCfg.monitor, htrA, hmid_cfg, (hD (A.scan qA)).1]
              · simp [t_2, t_1, p_2, p_1, j, cA1, LocatedCfg.monitor, htrA, hmid_cfg, hi, hD i]
            have hM3 : ∀ i, p_2 (tMark i) = cA1.position i ∧
                MarkExact (t_3 (tMark i)) (p_2 (tMark i)) (cA1.lower i) (cA1.upper i) := by
              intro i
              by_cases hi : i = j
              · subst i
                have hp2M : p_2 (tMark j) = pos1M := by simp [p_2]
                rw [hp2M, hpos_eq2]; exact ⟨rfl, hpos_eq2 ▸ hM3_exact⟩
              · have hne : (tMark i : RTape A.tapeCount) ≠ tMark j := by simp [hi]
                rw [htr3_out (tMark i) hne]
                have ht2i : t_2 (tMark i) = t (tMark i) := by simp [t_2, t_1, hi]
                have hp2i : p_2 (tMark i) = p (tMark i) := by simp [p_2, p_1, hi]
                have hci : cA1.position i = posA i ∧ cA1.lower i = lowA i ∧ cA1.upper i = uppA i := by
                  simp [j, cA1, LocatedCfg.monitor, htrA, hi]
                rw [ht2i, hp2i, hci.1, hci.2.1, hci.2.2]; exact hM i
            obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hio, hpio, hlio, huio, hDf, hMf, hw_f, henv_f⟩ :=
              ih hrest' t_3 p_2 l_2 u_2 L_env U_env hcA1_st hw2 henv2 hwA1 hsup1 hD3 hM3 hbd1
            have hpre := trace_prepend2 hstep1 hstep2 htrB
            refine ⟨t1, p1, l1, u1, (2 + nB) + n1, Trace.append hpre htail, by omega,
              ?_, ?_, ?_, ?_, hDf, hMf, hw_f, henv_f⟩
            · rw [hio, htr3_out tIO (by simp)]; simp [t_2, t_1]
            · rw [hpio]; simp [p_2, p_1]
            · rw [hlio]; simp [l_2, l_1]
            · rw [huio]; simp [u_2, u_1]

private theorem rPhase_outRead (output : List Bool) (p_out0 L_out U_out : ℤ)
    (t : RCfg A) (p l u L_env U_env : RPos A)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r) (henv : ∀ r, L_env r ≤ l r ∧ u r ≤ U_env r)
    (hio_env : L_env tIO ≤ 0 ∧ (output.length : ℤ) ≤ U_env tIO)
    (hD_env : L_env (tData outA) ≤ L_out ∧ U_out + 1 ≤ U_env (tData outA))
    (hM_env : L_env (tMark outA) ≤ L_out ∧ U_out + 1 ≤ U_env (tMark outA))
    (hpio : p tIO = 0) (htio : IsWordAt (t tIO) 0 [])
    (hpD : p (tData outA) = p_out0)
    (htD : ∀ z : ℤ, absCell (t (tData outA)) p_out0 z =
      if h : p_out0 ≤ z ∧ (z - p_out0).toNat < output.length then some output[(z - p_out0).toNat] else none)
    (hpM : p (tMark outA) = p_out0)
    (hmM : MarkExact (t (tMark outA)) p_out0 L_out U_out)
    (hsup : ∀ k < output.length, L_out ≤ p_out0 + k ∧ p_out0 + k ≤ U_out) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (resetMachine A outA)) n
        (cCfg (rOps A outA) (rStart A) tIO (.inr qOutRead) t p l u)
        (cCfg (rOps A outA) (rStart A) tIO (.inr qRewIOStart) t1 p1 l1 u1) ∧
      n ≤ 7 * output.length + 1 ∧
      (∀ r, r ≠ tIO → r ≠ tData outA → r ≠ tMark outA →
        t1 r = t r ∧ p1 r = p r ∧ l1 r = l r ∧ u1 r = u r) ∧
      IsWordAt (t1 tIO) (output.length : ℤ) output ∧ p1 tIO = output.length ∧
      p1 (tData outA) = p_out0 + output.length ∧ p1 (tMark outA) = p_out0 + output.length ∧
      MarkExact (t1 (tMark outA)) (p_out0 + output.length) L_out (max U_out (p_out0 + output.length)) ∧
      DataSupported (t1 (tData outA)) (p_out0 + output.length) L_out (max U_out (p_out0 + output.length)) ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
  have ind : ∀ (rem k : ℕ) (hk : k ≤ output.length) (hrem : output.length - k = rem)
      (t' : RCfg A) (p' l' u' : RPos A)
      (hw' : ∀ r, l' r ≤ p' r ∧ p' r ≤ u' r) (henv' : ∀ r, L_env r ≤ l' r ∧ u' r ≤ U_env r)
      (hpio' : p' tIO = k) (htio' : IsWordAt (t' tIO) (k : ℤ) (output.take k))
      (hpD' : p' (tData outA) = p_out0 + k)
      (htD' : ∀ z : ℤ, absCell (t' (tData outA)) (p_out0 + k) z =
        if h : p_out0 ≤ z ∧ (z - p_out0).toNat < output.length then some output[(z - p_out0).toNat] else none)
      (hpM' : p' (tMark outA) = p_out0 + k)
      (hmM' : MarkExact (t' (tMark outA)) (p_out0 + k) L_out (max U_out (p_out0 + k))),
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (resetMachine A outA)) n
          (cCfg (rOps A outA) (rStart A) tIO (.inr qOutRead) t' p' l' u')
          (cCfg (rOps A outA) (rStart A) tIO (.inr qRewIOStart) t1 p1 l1 u1) ∧
        n ≤ 7 * rem + 1 ∧
        (∀ r, r ≠ tIO → r ≠ tData outA → r ≠ tMark outA →
          t1 r = t' r ∧ p1 r = p' r ∧ l1 r = l' r ∧ u1 r = u' r) ∧
        IsWordAt (t1 tIO) (output.length : ℤ) output ∧ p1 tIO = output.length ∧
        p1 (tData outA) = p_out0 + output.length ∧ p1 (tMark outA) = p_out0 + output.length ∧
        MarkExact (t1 (tMark outA)) (p_out0 + output.length) L_out (max U_out (p_out0 + output.length)) ∧
        DataSupported (t1 (tData outA)) (p_out0 + output.length) L_out (max U_out (p_out0 + output.length)) ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
    intro rem
    induction rem with
    | zero =>
      intro k hk hrem t' p' l' u' hw' henv' hpio' htio' hpD' htD' hpM' hmM'
      have hkeq : k = output.length := by omega
      subst hkeq
      have hhead : (t' (tData outA)).head = none := by
        rw [← absCell_self (t' (tData outA)) (p' (tData outA)), hpD', htD']; simp
      have hs := rStep_branch A outA
        (q := qOutRead) (k := tData outA) rfl t' p' l' u' (hw' (tData outA))
      rw [hhead] at hs
      have hdsup : DataSupported (t' (tData outA)) (p_out0 + output.length) L_out (max U_out (p_out0 + output.length)) := by
        intro z hz
        rw [htD'] at hz
        split_ifs at hz with h
        · have hidx := hsup (z - p_out0).toNat h.2
          have hz_eq : p_out0 + ((z - p_out0).toNat : ℤ) = z := by omega
          rw [hz_eq] at hidx
          exact ⟨hidx.1, le_trans hidx.2 (le_max_left _ _)⟩
        · exact (hz rfl).elim
      refine ⟨t', p', l', u', 1, .cons hs (.refl _), le_rfl, fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩,
        by simpa using htio', hpio', hpD', hpM', hmM', hdsup, hw', henv'⟩
    | succ r ih =>
      intro k hk hrem t' p' l' u' hw' henv' hpio' htio' hpD' htD' hpM' hmM'
      have hlt : k < output.length := by omega
      let b := output[k]
      have hsupk := hsup k hlt
      have hheadD : (t' (tData outA)).head = some b := by
        rw [← absCell_self (t' (tData outA)) (p' (tData outA)), hpD', htD']
        have hc : p_out0 ≤ p_out0 + (k : ℤ) ∧ ((p_out0 + (k : ℤ)) - p_out0).toNat < output.length := ⟨by omega, by simpa⟩
        rw [dif_pos hc]; simp [b]
      have hs0 := rStep_branch A outA
        (q := qOutRead) (k := tData outA) rfl t' p' l' u' (hw' (tData outA))
      rw [hheadD] at hs0
      have hs1 := rStep_write A outA
        (q := qOutWriteIO b) (q' := qOutAdvIO) (k := tIO) (sym := some b)
        (rOps_outWriteIO A outA b) t' p' l' u' (hw' tIO)
      let t_1 := Function.update t' tIO ((t' tIO).write (some b))
      have hs2 := rStep_move_right A outA
        (q := qOutAdvIO) (q' := qOutAdvD) (k := tIO) rfl t_1 p' l' u'
      let t_2 := Function.update t_1 tIO ((t_1 tIO).move .right)
      let p_2 := Function.update p' tIO (p' tIO + 1)
      let l_2 := Function.update l' tIO (min (l' tIO) (p' tIO + 1))
      let u_2 := Function.update u' tIO (max (u' tIO) (p' tIO + 1))
      have hs3 := rStep_move_right A outA
        (q := qOutAdvD) (q' := qOutAdvM) (k := tData outA) rfl t_2 p_2 l_2 u_2
      let t_3 := Function.update t_2 (tData outA) ((t_2 (tData outA)).move .right)
      let p_3 := Function.update p_2 (tData outA) (p_2 (tData outA) + 1)
      let l_3 := Function.update l_2 (tData outA) (min (l_2 (tData outA)) (p_2 (tData outA) + 1))
      let u_3 := Function.update u_2 (tData outA) (max (u_2 (tData outA)) (p_2 (tData outA) + 1))
      have hs4 := rStep_move_right A outA
        (q := qOutAdvM) (q' := qOutCheckM) (k := tMark outA) rfl t_3 p_3 l_3 u_3
      let t_4 := Function.update t_3 (tMark outA) ((t_3 (tMark outA)).move .right)
      let p_4 := Function.update p_3 (tMark outA) (p_3 (tMark outA) + 1)
      let l_4 := Function.update l_3 (tMark outA) (min (l_3 (tMark outA)) (p_3 (tMark outA) + 1))
      let u_4 := Function.update u_3 (tMark outA) (max (u_3 (tMark outA)) (p_3 (tMark outA) + 1))
      have hne_d_io : (tData outA : RTape A.tapeCount) ≠ tIO := by simp
      have hne_m_io : (tMark outA : RTape A.tapeCount) ≠ tIO := by simp
      have hne_m_d : (tMark outA : RTape A.tapeCount) ≠ tData outA := by simp
      have hp4io : p_4 tIO = ((k + 1 : ℕ) : ℤ) := by
        simp [p_4, p_3, p_2, hpio']; try omega
      have hp4D : p_4 (tData outA) = p_out0 + ((k + 1 : ℕ) : ℤ) := by
        simp [p_4, p_3, p_2, hpD']; try omega
      have hp4M : p_4 (tMark outA) = p_out0 + ((k + 1 : ℕ) : ℤ) := by
        simp [p_4, p_3, p_2, hpM']; try omega
      have hw4 : ∀ r', l_4 r' ≤ p_4 r' ∧ p_4 r' ≤ u_4 r' := by
        intro r'
        rcases r' with _ | j | j
        · simp [p_4, p_3, p_2, l_4, l_3, l_2, u_4, u_3, u_2]
        · by_cases hj : j = outA
          · subst j; simp [p_4, p_3, p_2, l_4, l_3, l_2, u_4, u_3, u_2]
          · simp [p_4, p_3, p_2, l_4, l_3, l_2, u_4, u_3, u_2, hj, hw' (tData j)]
        · by_cases hj : j = outA
          · subst j; simp [p_4, p_3, p_2, l_4, l_3, l_2, u_4, u_3, u_2]
          · simp [p_4, p_3, p_2, l_4, l_3, l_2, u_4, u_3, u_2, hj, hw' (tMark j)]
      have henv4 : ∀ r', L_env r' ≤ l_4 r' ∧ u_4 r' ≤ U_env r' := by
        intro r'
        rcases r' with _ | j | j
        · have h1 := henv' tIO
          have hlo : l_4 tIO = min (l' tIO) (p' tIO + 1) := by
            dsimp [l_4, l_3, l_2]
            rw [Function.update_of_ne hne_m_io.symm, Function.update_of_ne hne_d_io.symm, Function.update_self]
          have hhi : u_4 tIO = max (u' tIO) (p' tIO + 1) := by
            dsimp [u_4, u_3, u_2]
            rw [Function.update_of_ne hne_m_io.symm, Function.update_of_ne hne_d_io.symm, Function.update_self]
          change L_env tIO ≤ l_4 tIO ∧ u_4 tIO ≤ U_env tIO
          rw [hlo, hhi, hpio']
          exact ⟨le_min h1.1 (by have := hio_env.1; omega), max_le h1.2 (by have := hio_env.2; omega)⟩
        · by_cases hj : j = outA
          · subst j; have h1 := henv' (tData outA)
            have hlo : l_4 (tData outA) = min (l' (tData outA)) (p' (tData outA) + 1) := by
              dsimp [l_4, l_3, l_2, p_2]
              rw [Function.update_of_ne hne_m_d.symm, Function.update_self, Function.update_of_ne hne_d_io,
                  Function.update_of_ne hne_d_io]
            have hhi : u_4 (tData outA) = max (u' (tData outA)) (p' (tData outA) + 1) := by
              dsimp [u_4, u_3, u_2, p_2]
              rw [Function.update_of_ne hne_m_d.symm, Function.update_self, Function.update_of_ne hne_d_io,
                  Function.update_of_ne hne_d_io]
            change L_env (tData outA) ≤ l_4 (tData outA) ∧ u_4 (tData outA) ≤ U_env (tData outA)
            rw [hlo, hhi, hpD']
            exact ⟨le_min h1.1 (by have := hD_env.1; omega), max_le h1.2 (by have := hD_env.2; omega)⟩
          · simp [l_4, u_4, l_3, u_3, l_2, u_2, hj, henv' (tData j)]
        · by_cases hj : j = outA
          · subst j; have h1 := henv' (tMark outA)
            have hlo : l_4 (tMark outA) = min (l' (tMark outA)) (p' (tMark outA) + 1) := by
              dsimp [l_4, l_3, l_2, p_3, p_2]
              rw [Function.update_self, Function.update_of_ne hne_m_d, Function.update_of_ne hne_m_io,
                  Function.update_of_ne hne_m_d, Function.update_of_ne hne_m_io]
            have hhi : u_4 (tMark outA) = max (u' (tMark outA)) (p' (tMark outA) + 1) := by
              dsimp [u_4, u_3, u_2, p_3, p_2]
              rw [Function.update_self, Function.update_of_ne hne_m_d, Function.update_of_ne hne_m_io,
                  Function.update_of_ne hne_m_d, Function.update_of_ne hne_m_io]
            change L_env (tMark outA) ≤ l_4 (tMark outA) ∧ u_4 (tMark outA) ≤ U_env (tMark outA)
            rw [hlo, hhi, hpM']
            exact ⟨le_min h1.1 (by have := hM_env.1; omega), max_le h1.2 (by have := hM_env.2; omega)⟩
          · simp [l_4, u_4, l_3, u_3, l_2, u_2, hj, henv' (tMark j)]
      have ht4_io : IsWordAt (t_4 tIO) ((k + 1 : ℕ) : ℤ) (output.take (k + 1)) := by
        intro z
        have heq : t_4 tIO = ((t' tIO).write (some b)).move .right := by
          simp [t_4, t_3, t_2, t_1]
        rw [heq, show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by omega, absCell_move_right, absCell_write,
          htio' z]
        have hlen_t : (output.take k).length = k := List.length_take_of_le (by omega)
        have hlen_t1 : (output.take (k + 1)).length = k + 1 := List.length_take_of_le hlt
        by_cases hz : z = k
        · subst z; rw [if_pos rfl, dif_pos ⟨Int.natCast_nonneg k, by omega⟩]
          simp [b, List.getElem_take]
        · rw [if_neg hz]
          by_cases h0 : 0 ≤ z ∧ z.toNat < k
          · have h0a : 0 ≤ z ∧ z.toNat < (output.take k).length := ⟨h0.1, by rw [hlen_t]; exact h0.2⟩
            have h0b : 0 ≤ z ∧ z.toNat < (output.take (k + 1)).length := ⟨h0.1, by rw [hlen_t1]; omega⟩
            rw [dif_pos h0a, dif_pos h0b]; simp [List.getElem_take]
          · have h0a : ¬ (0 ≤ z ∧ z.toNat < (output.take k).length) := by rw [hlen_t]; exact h0
            have h0b : ¬ (0 ≤ z ∧ z.toNat < (output.take (k + 1)).length) := by
              rw [hlen_t1]; intro h; apply h0; exact ⟨h.1, by omega⟩
            rw [dif_neg h0a, dif_neg h0b]
      have ht4_D : ∀ z : ℤ, absCell (t_4 (tData outA)) (p_out0 + ((k + 1 : ℕ) : ℤ)) z =
          if h : p_out0 ≤ z ∧ (z - p_out0).toNat < output.length then some output[(z - p_out0).toNat] else none := by
        intro z
        have heq : t_4 (tData outA) = (t' (tData outA)).move .right := by simp [t_4, t_3, t_2, t_1]
        rw [heq, show p_out0 + ((k + 1 : ℕ) : ℤ) = (p_out0 + (k : ℤ)) + 1 by omega,
          absCell_move_right, htD' z]
      have ht4M_cell : ∀ z : ℤ, absCell (t_4 (tMark outA)) (p_out0 + ((k + 1 : ℕ) : ℤ)) z =
          if z = 0 then some false else if L_out ≤ z ∧ z ≤ max U_out (p_out0 + (k : ℤ)) then some true else none := by
        intro z
        have heq : t_4 (tMark outA) = (t' (tMark outA)).move .right := by simp [t_4, t_3, t_2, t_1]
        rw [heq, show p_out0 + ((k + 1 : ℕ) : ℤ) = (p_out0 + (k : ℤ)) + 1 by omega,
          absCell_move_right, hmM'.2.2.2.2 z]
      have hs5 := rStep_branch A outA
        (q := qOutCheckM) (k := tMark outA) rfl t_4 p_4 l_4 u_4 (hw4 (tMark outA))
      let u_prev := max U_out (p_out0 + (k : ℤ))
      let u_next := max U_out (p_out0 + ((k + 1 : ℕ) : ℤ))
      have hu_pre : u_prev = U_out := max_eq_left hsupk.2
      have hmM_branch : ∃ t_5 nB,
          Computation.Trace (locatedStep (resetMachine A outA)) nB
            (cCfg (rOps A outA) (rStart A) tIO (.inr qOutCheckM) t_4 p_4 l_4 u_4)
            (cCfg (rOps A outA) (rStart A) tIO (.inr qOutRead) t_5 p_4 l_4 u_4) ∧
          nB ≤ 2 ∧
          (∀ r ≠ tMark outA, t_5 r = t_4 r) ∧
          MarkExact (t_5 (tMark outA)) (p_out0 + ((k + 1 : ℕ) : ℤ)) L_out u_next := by
        have hhd4M : (t_4 (tMark outA)).head =
            if p_out0 + ((k + 1 : ℕ) : ℤ) = 0 then some false
            else if L_out ≤ p_out0 + ((k + 1 : ℕ) : ℤ) ∧ p_out0 + ((k + 1 : ℕ) : ℤ) ≤ u_prev then some true
            else none := by
          rw [← absCell_self (t_4 (tMark outA)) (p_4 (tMark outA)), hp4M]; exact ht4M_cell _
        by_cases hle : p_out0 + ((k + 1 : ℕ) : ℤ) ≤ u_prev
        · have hlo : L_out ≤ p_out0 + ((k + 1 : ℕ) : ℤ) := by have := hsupk.1; omega
          have hne : (t_4 (tMark outA)).head ≠ none := by
            rw [hhd4M]
            split_ifs with h0 h1
            · simp
            · simp
            · exfalso; apply h1; exact ⟨hlo, by dsimp [u_prev] at hle ⊢; omega⟩
          have hu_eq : u_next = u_prev := by
            dsimp [u_next]; rw [hu_pre]; exact max_eq_left (by omega)
          rcases Option.ne_none_iff_exists'.1 hne with ⟨symM, hsM⟩
          rw [hsM] at hs5
          refine ⟨t_4, 1, .cons hs5 (.refl _), by omega, fun _ _ => rfl, ?_⟩
          rw [hu_eq]
          exact ⟨hmM'.1, by have := hmM'.2.1; omega, hlo, hle, ht4M_cell⟩
        · have hp_gt : p_out0 + ((k + 1 : ℕ) : ℤ) = u_prev + 1 := by omega
          have hne0 : p_out0 + ((k + 1 : ℕ) : ℤ) ≠ 0 := by have := hmM'.2.1; omega
          have hhd_none : (t_4 (tMark outA)).head = none := by
            rw [hhd4M, if_neg hne0, if_neg (by intro h; exact hle h.2)]
          rw [hhd_none] at hs5
          have hs6 := rStep_write A outA
            (q := qOutWriteM) (q' := qOutRead) (k := tMark outA) (sym := some true) rfl
            t_4 p_4 l_4 u_4 (hw4 (tMark outA))
          refine ⟨Function.update t_4 (tMark outA) ((t_4 (tMark outA)).write (some true)), 2,
            .cons hs5 (.cons hs6 (.refl _)), le_rfl, fun r hr => Function.update_of_ne hr _ _, ?_⟩
          have hL_le : L_out ≤ p_out0 + ((k + 1 : ℕ) : ℤ) := by have := hsupk.1; omega
          have h0_le : 0 ≤ u_next := by have := hmM'.2.1; dsimp [u_next, u_prev] at *; omega
          refine ⟨hmM'.1, h0_le, hL_le, le_max_right _ _, ?_⟩
          intro z
          rw [Function.update_self, absCell_write, ht4M_cell z]
          have hle_unext : u_next = u_prev + 1 := by dsimp [u_next, u_prev] at hle hp_gt ⊢; omega
          rw [hle_unext]
          by_cases hz : z = u_prev + 1
          · subst z
            rw [show (u_prev + 1 = p_out0 + ((k + 1 : ℕ) : ℤ)) from hp_gt.symm, if_pos rfl,
              if_neg hne0, if_pos (by have := hsupk.1; omega)]
          · rw [if_neg (by omega)]
            split_ifs with hz0 h1 h2 <;> first | rfl | omega
      obtain ⟨t_5, nB, htrB, hnB, ht5_out, hmM5⟩ := hmM_branch
      have ht5_io : IsWordAt (t_5 tIO) ((k + 1 : ℕ) : ℤ) (output.take (k + 1)) := by
        rw [ht5_out tIO hne_m_io.symm]; exact ht4_io
      have ht5_D : ∀ z : ℤ, absCell (t_5 (tData outA)) (p_out0 + ((k + 1 : ℕ) : ℤ)) z =
          if h : p_out0 ≤ z ∧ (z - p_out0).toNat < output.length then some output[(z - p_out0).toNat] else none := by
        rw [ht5_out (tData outA) hne_m_d.symm]; exact ht4_D
      obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hout1, ht1_io, hp1io, hp1D, hp1M, hmM1, hD1, hw_f, henv_f⟩ :=
        ih (k + 1) hlt (by omega) t_5 p_4 l_4 u_4 hw4 henv4 hp4io ht5_io hp4D ht5_D hp4M hmM5
      have hpre : Computation.Trace (locatedStep (resetMachine A outA)) (5 + nB)
          (cCfg (rOps A outA) (rStart A) tIO (.inr qOutRead) t' p' l' u')
          (cCfg (rOps A outA) (rStart A) tIO (.inr qOutRead) t_5 p_4 l_4 u_4) := by
        have ha : Computation.Trace (locatedStep (resetMachine A outA)) 5
            (cCfg (rOps A outA) (rStart A) tIO (.inr qOutRead) t' p' l' u')
            (cCfg (rOps A outA) (rStart A) tIO (.inr qOutCheckM) t_4 p_4 l_4 u_4) :=
          .cons hs0 (.cons hs1 (.cons hs2 (.cons hs3 (.cons hs4 (.refl _)))))
        exact Trace.append ha htrB
      refine ⟨t1, p1, l1, u1, (5 + nB) + n1, Trace.append hpre htail, by omega, ?_,
        ht1_io, hp1io, hp1D, hp1M, hmM1, hD1, hw_f, henv_f⟩
      intro r hr1 hr2 hr3
      have ho := hout1 r hr1 hr2 hr3
      have hr4 : t_5 r = t' r ∧ p_4 r = p' r ∧ l_4 r = l' r ∧ u_4 r = u' r := by
        rw [ht5_out r hr3]
        simp [t_4, t_3, t_2, t_1, p_4, p_3, p_2, l_4, l_3, l_2, u_4, u_3, u_2, hr1, hr2, hr3]
      exact ⟨ho.1.trans hr4.1, ho.2.1.trans hr4.2.1, ho.2.2.1.trans hr4.2.2.1, ho.2.2.2.trans hr4.2.2.2⟩
  exact ind output.length 0 (Nat.zero_le _) (Nat.sub_zero _) t p l u hw henv hpio
    (by simpa using htio) (by simpa using hpD) (by simpa using htD) (by simpa using hpM)
    (by simpa [hmM.2.2.2.1] using hmM)

private theorem rPhase_wipeS1 (j : Fin A.tapeCount) (L U : ℤ)
    (t : RCfg A) (p l u L_env U_env : RPos A)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r) (henv : ∀ r, L_env r ≤ l r ∧ u r ≤ U_env r)
    (hD_env : L_env (tData j) ≤ L - 1 ∧ U + 1 ≤ U_env (tData j))
    (hM_env : L_env (tMark j) ≤ L - 1 ∧ U + 1 ≤ U_env (tMark j))
    (h0U : 0 ≤ U)
    (hpeq : p (tMark j) = p (tData j)) (hlo : L ≤ p (tMark j)) (hhi : p (tMark j) ≤ U + 1)
    (hmM : ∀ z : ℤ, absCell (t (tMark j)) (p (tMark j)) z =
      if z = 0 then some false else if L ≤ z ∧ z ≤ U then some true else none) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (resetMachine A outA)) n
        (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS1Check j)) t p l u)
        (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS2BackD j)) t1 p1 l1 u1) ∧
      n ≤ 3 * (U + 1 - p (tMark j)).toNat + 1 ∧
      (∀ r, r ≠ tData j → r ≠ tMark j → t1 r = t r ∧ p1 r = p r ∧ l1 r = l r ∧ u1 r = u r) ∧
      p1 (tData j) = U + 1 ∧ p1 (tMark j) = U + 1 ∧
      (∀ z : ℤ, absCell (t1 (tData j)) (p1 (tData j)) z = absCell (t (tData j)) (p (tData j)) z) ∧
      (∀ z : ℤ, absCell (t1 (tMark j)) (p1 (tMark j)) z = absCell (t (tMark j)) (p (tMark j)) z) ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
  have ind : ∀ (rem : ℕ) (t' : RCfg A) (p' l' u' : RPos A)
      (hw' : ∀ r, l' r ≤ p' r ∧ p' r ≤ u' r) (henv' : ∀ r, L_env r ≤ l' r ∧ u' r ≤ U_env r)
      (hpeq' : p' (tMark j) = p' (tData j)) (hlo' : L ≤ p' (tMark j)) (hhi' : p' (tMark j) ≤ U + 1)
      (hrem : (U + 1 - p' (tMark j)).toNat = rem)
      (hmM' : ∀ z : ℤ, absCell (t' (tMark j)) (p' (tMark j)) z =
        if z = 0 then some false else if L ≤ z ∧ z ≤ U then some true else none),
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (resetMachine A outA)) n
          (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS1Check j)) t' p' l' u')
          (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS2BackD j)) t1 p1 l1 u1) ∧
        n ≤ 3 * rem + 1 ∧
        (∀ r, r ≠ tData j → r ≠ tMark j → t1 r = t' r ∧ p1 r = p' r ∧ l1 r = l' r ∧ u1 r = u' r) ∧
        p1 (tData j) = U + 1 ∧ p1 (tMark j) = U + 1 ∧
        (∀ z : ℤ, absCell (t1 (tData j)) (p1 (tData j)) z = absCell (t' (tData j)) (p' (tData j)) z) ∧
        (∀ z : ℤ, absCell (t1 (tMark j)) (p1 (tMark j)) z = absCell (t' (tMark j)) (p' (tMark j)) z) ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
    intro rem
    induction rem with
    | zero =>
      intro t' p' l' u' hw' henv' hpeq' hlo' hhi' hrem hmM'
      have hpU1 : p' (tMark j) = U + 1 := by omega
      have hhead : (t' (tMark j)).head = none := by
        rw [← absCell_self (t' (tMark j)) (p' (tMark j)), hmM', hpU1]
        rw [if_neg (by omega), if_neg (by omega)]
      have hs := rStep_branch A outA
        (q := qWipeS1Check j) (k := tMark j) rfl t' p' l' u' (hw' (tMark j))
      rw [hhead] at hs
      exact ⟨t', p', l', u', 1, .cons hs (.refl _), le_rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩,
        by omega, hpU1, fun _ => rfl, fun _ => rfl, hw', henv'⟩
    | succ r ih =>
      intro t' p' l' u' hw' henv' hpeq' hlo' hhi' hrem hmM'
      have hp_leU : p' (tMark j) ≤ U := by omega
      have hne : (t' (tMark j)).head ≠ none := by
        rw [← absCell_self (t' (tMark j)) (p' (tMark j)), hmM']
        split_ifs with h0 h1
        · simp
        · simp
        · exact absurd ⟨hlo', hp_leU⟩ h1
      rcases Option.ne_none_iff_exists'.1 hne with ⟨sym, hhead⟩
      have hs0 := rStep_branch A outA
        (q := qWipeS1Check j) (k := tMark j) rfl t' p' l' u' (hw' (tMark j))
      rw [hhead] at hs0
      have hs1 := rStep_move_right A outA
        (q := qWipeS1AdvD j) (q' := qWipeS1AdvM j) (k := tData j) rfl t' p' l' u'
      let t_1 := Function.update t' (tData j) ((t' (tData j)).move .right)
      let p_1 := Function.update p' (tData j) (p' (tData j) + 1)
      let l_1 := Function.update l' (tData j) (min (l' (tData j)) (p' (tData j) + 1))
      let u_1 := Function.update u' (tData j) (max (u' (tData j)) (p' (tData j) + 1))
      have hs2 := rStep_move_right A outA
        (q := qWipeS1AdvM j) (q' := qWipeS1Check j) (k := tMark j) rfl t_1 p_1 l_1 u_1
      let t_2 := Function.update t_1 (tMark j) ((t_1 (tMark j)).move .right)
      let p_2 := Function.update p_1 (tMark j) (p_1 (tMark j) + 1)
      let l_2 := Function.update l_1 (tMark j) (min (l_1 (tMark j)) (p_1 (tMark j) + 1))
      let u_2 := Function.update u_1 (tMark j) (max (u_1 (tMark j)) (p_1 (tMark j) + 1))
      have hw2 : ∀ r', l_2 r' ≤ p_2 r' ∧ p_2 r' ≤ u_2 r' := by
        intro r'; rcases r' with _ | i | i
        · simp only [p_2, p_1, l_2, l_1, u_2, u_1, Function.update_of_ne (by simp : tIO ≠ tMark j),
            Function.update_of_ne (by simp : tIO ≠ tData j)]; exact hw' tIO
        · by_cases hi : i = j
          · subst i; simp only [p_2, p_1, l_2, l_1, u_2, u_1,
              Function.update_of_ne (by simp : (tData j : RTape A.tapeCount) ≠ tMark j), Function.update_self]
            exact ⟨min_le_right _ _, le_max_right _ _⟩
          · have h1 : (tData i : RTape A.tapeCount) ≠ tData j := fun h => hi (Sum.inl.inj (Sum.inr.inj h))
            simp only [p_2, p_1, l_2, l_1, u_2, u_1,
              Function.update_of_ne (by simp : (tData i : RTape A.tapeCount) ≠ tMark j),
              Function.update_of_ne h1]; exact hw' (tData i)
        · by_cases hi : i = j
          · subst i; simp only [p_2, p_1, l_2, l_1, u_2, u_1, Function.update_self]
            exact ⟨min_le_right _ _, le_max_right _ _⟩
          · have h2 : (tMark i : RTape A.tapeCount) ≠ tMark j := fun h => hi (Sum.inr.inj (Sum.inr.inj h))
            simp only [p_2, p_1, l_2, l_1, u_2, u_1, Function.update_of_ne h2,
              Function.update_of_ne (by simp : (tMark i : RTape A.tapeCount) ≠ tData j)]; exact hw' (tMark i)
      have henv2 : ∀ r', L_env r' ≤ l_2 r' ∧ u_2 r' ≤ U_env r' := by
        intro r'; rcases r' with _ | i | i
        · simp only [l_2, l_1, u_2, u_1, Function.update_of_ne (by simp : tIO ≠ tMark j),
            Function.update_of_ne (by simp : tIO ≠ tData j)]; exact henv' tIO
        · by_cases hi : i = j
          · subst i; have h1 := henv' (tData j)
            change L_env (tData j) ≤ l_2 (tData j) ∧ u_2 (tData j) ≤ U_env (tData j)
            simp only [l_2, u_2, l_1, u_1, Function.update_of_ne (by simp : (tData j : RTape A.tapeCount) ≠ tMark j),
              Function.update_self]
            exact ⟨le_min h1.1 (by have := hD_env.1; omega), max_le h1.2 (by have := hD_env.2; omega)⟩
          · have h1 : (tData i : RTape A.tapeCount) ≠ tData j := fun h => hi (Sum.inl.inj (Sum.inr.inj h))
            simp only [l_2, l_1, u_2, u_1,
              Function.update_of_ne (by simp : (tData i : RTape A.tapeCount) ≠ tMark j),
              Function.update_of_ne h1]; exact henv' (tData i)
        · by_cases hi : i = j
          · subst i; have h1 := henv' (tMark j)
            change L_env (tMark j) ≤ l_2 (tMark j) ∧ u_2 (tMark j) ≤ U_env (tMark j)
            simp only [l_2, u_2, l_1, u_1, p_1, Function.update_self,
              Function.update_of_ne (by simp : (tMark j : RTape A.tapeCount) ≠ tData j)]
            exact ⟨le_min h1.1 (by have := hM_env.1; omega), max_le h1.2 (by have := hM_env.2; omega)⟩
          · have h2 : (tMark i : RTape A.tapeCount) ≠ tMark j := fun h => hi (Sum.inr.inj (Sum.inr.inj h))
            simp only [l_2, l_1, u_2, u_1, Function.update_of_ne h2,
              Function.update_of_ne (by simp : (tMark i : RTape A.tapeCount) ≠ tData j)]; exact henv' (tMark i)
      have hp2M : p_2 (tMark j) = p' (tMark j) + 1 := by simp [p_2, p_1]
      have hmM2 : ∀ z : ℤ, absCell (t_2 (tMark j)) (p_2 (tMark j)) z =
          if z = 0 then some false else if L ≤ z ∧ z ≤ U then some true else none := by
        intro z
        have heq : t_2 (tMark j) = (t' (tMark j)).move .right := by simp [t_2, t_1]
        rw [heq, hp2M, absCell_move_right, hmM' z]
      obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hout1, hp1D, hp1M, ht1D, ht1M, hw1, henv1⟩ :=
        ih t_2 p_2 l_2 u_2 hw2 henv2 (by simp [p_2, p_1, hpeq']) (by omega) (by omega) (by omega) hmM2
      refine ⟨t1, p1, l1, u1, 3 + n1, trace_prepend3 hs0 hs1 hs2 htail, by omega, ?_,
        hp1D, hp1M, ?_, ?_, hw1, henv1⟩
      · intro r hr1 hr2
        have ho := hout1 r hr1 hr2
        have hr' : t_2 r = t' r ∧ p_2 r = p' r ∧ l_2 r = l' r ∧ u_2 r = u' r := by
          dsimp [t_2, t_1, p_2, p_1, l_2, l_1, u_2, u_1]
          simp only [Function.update_of_ne hr2, Function.update_of_ne hr1, and_self]
        exact ⟨ho.1.trans hr'.1, ho.2.1.trans hr'.2.1, ho.2.2.1.trans hr'.2.2.1, ho.2.2.2.trans hr'.2.2.2⟩
      · intro z; rw [ht1D z, show t_2 (tData j) = (t' (tData j)).move .right by simp [t_2, t_1],
          show p_2 (tData j) = p' (tData j) + 1 by simp [p_2, p_1], absCell_move_right]
      · intro z; rw [ht1M z, show t_2 (tMark j) = (t' (tMark j)).move .right by simp [t_2, t_1],
          hp2M, absCell_move_right]
  exact ind (U + 1 - p (tMark j)).toNat t p l u hw henv hpeq hlo hhi rfl hmM

private theorem rPhase_wipeS2 (j : Fin A.tapeCount) (L U : ℤ)
    (t : RCfg A) (p l u L_env U_env : RPos A)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r) (henv : ∀ r, L_env r ≤ l r ∧ u r ≤ U_env r)
    (hD_env : L_env (tData j) ≤ L - 1 ∧ U + 1 ≤ U_env (tData j))
    (hM_env : L_env (tMark j) ≤ L - 1 ∧ U + 1 ≤ U_env (tMark j))
    (hL0 : L ≤ 0) (rem : ℕ)
    (hpD : p (tData j) = rem) (hpM : p (tMark j) = rem) (hrem_le : (rem : ℤ) ≤ U)
    (hD_hi : ∀ z > (rem : ℤ), absCell (t (tData j)) (rem : ℤ) z = none)
    (hD_lo : ∀ z < L, absCell (t (tData j)) (rem : ℤ) z = none)
    (hmM : ∀ z : ℤ, absCell (t (tMark j)) (rem : ℤ) z =
      if z = 0 then some false else if L ≤ z ∧ z ≤ (rem : ℤ) then some true else none) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (resetMachine A outA)) n
        (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS2Check j)) t p l u)
        (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS3Check j)) t1 p1 l1 u1) ∧
      n ≤ 5 * rem + 1 ∧
      (∀ r, r ≠ tData j → r ≠ tMark j → t1 r = t r ∧ p1 r = p r ∧ l1 r = l r ∧ u1 r = u r) ∧
      p1 (tData j) = 0 ∧ p1 (tMark j) = 0 ∧
      (∀ z ≥ 1, absCell (t1 (tData j)) 0 z = none ∧ absCell (t1 (tMark j)) 0 z = none) ∧
      (∀ z < L, absCell (t1 (tData j)) 0 z = none) ∧
      (∀ z : ℤ, absCell (t1 (tMark j)) 0 z =
        if z = 0 then some false else if L ≤ z ∧ z ≤ 0 then some true else none) ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
  have ind : ∀ (rem' : ℕ) (t' : RCfg A) (p' l' u' : RPos A)
      (hw' : ∀ r, l' r ≤ p' r ∧ p' r ≤ u' r) (henv' : ∀ r, L_env r ≤ l' r ∧ u' r ≤ U_env r)
      (hpD' : p' (tData j) = rem') (hpM' : p' (tMark j) = rem') (hrem_le' : (rem' : ℤ) ≤ U)
      (hD_hi' : ∀ z > (rem' : ℤ), absCell (t' (tData j)) (rem' : ℤ) z = none)
      (hD_lo' : ∀ z < L, absCell (t' (tData j)) (rem' : ℤ) z = none)
      (hmM' : ∀ z : ℤ, absCell (t' (tMark j)) (rem' : ℤ) z =
        if z = 0 then some false else if L ≤ z ∧ z ≤ (rem' : ℤ) then some true else none),
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (resetMachine A outA)) n
          (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS2Check j)) t' p' l' u')
          (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS3Check j)) t1 p1 l1 u1) ∧
        n ≤ 5 * rem' + 1 ∧
        (∀ r, r ≠ tData j → r ≠ tMark j → t1 r = t' r ∧ p1 r = p' r ∧ l1 r = l' r ∧ u1 r = u' r) ∧
        p1 (tData j) = 0 ∧ p1 (tMark j) = 0 ∧
        (∀ z ≥ 1, absCell (t1 (tData j)) 0 z = none ∧ absCell (t1 (tMark j)) 0 z = none) ∧
        (∀ z < L, absCell (t1 (tData j)) 0 z = none) ∧
        (∀ z : ℤ, absCell (t1 (tMark j)) 0 z =
          if z = 0 then some false else if L ≤ z ∧ z ≤ 0 then some true else none) ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
    intro rem'
    induction rem' with
    | zero =>
      intro t' p' l' u' hw' henv' hpD' hpM' hrem_le' hD_hi' hD_lo' hmM'
      have hhead : (t' (tMark j)).head = some false := by
        rw [← absCell_self (t' (tMark j)) (p' (tMark j)), hpM', hmM']; simp
      have hs := rStep_branch A outA
        (q := qWipeS2Check j) (k := tMark j) rfl t' p' l' u' (hw' (tMark j))
      rw [hhead] at hs
      exact ⟨t', p', l', u', 1, .cons hs (.refl _), le_rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩,
        hpD', hpM', fun z hz => ⟨hD_hi' z (by omega), by
          have hm := hmM' z; simp only [Nat.cast_zero] at hm
          rw [hm, if_neg (by omega), if_neg (by omega)]⟩,
        hD_lo', hmM', hw', henv'⟩
    | succ rem' ih =>
      intro t' p' l' u' hw' henv' hpD' hpM' hrem_le' hD_hi' hD_lo' hmM'
      have hhead : (t' (tMark j)).head = some true := by
        rw [← absCell_self (t' (tMark j)) (p' (tMark j)), hpM', hmM']
        rw [if_neg (by omega), if_pos ⟨by omega, le_rfl⟩]
      have hs0 := rStep_branch A outA
        (q := qWipeS2Check j) (k := tMark j) rfl t' p' l' u' (hw' (tMark j))
      rw [hhead] at hs0
      have hs1 := rStep_write A outA
        (q := qWipeS2ClrD j) (q' := qWipeS2ClrM j) (k := tData j) (sym := none) rfl t' p' l' u' (hw' (tData j))
      let t_1 := Function.update t' (tData j) ((t' (tData j)).write none)
      have hs2 := rStep_write A outA
        (q := qWipeS2ClrM j) (q' := qWipeS2StepD j) (k := tMark j) (sym := none) rfl t_1 p' l' u' (hw' (tMark j))
      let t_2 := Function.update t_1 (tMark j) ((t_1 (tMark j)).write none)
      have hs3 := rStep_move_left A outA
        (q := qWipeS2StepD j) (q' := qWipeS2StepM j) (k := tData j) rfl t_2 p' l' u'
      let t_3 := Function.update t_2 (tData j) ((t_2 (tData j)).move .left)
      let p_3 := Function.update p' (tData j) (p' (tData j) - 1)
      let l_3 := Function.update l' (tData j) (min (l' (tData j)) (p' (tData j) - 1))
      let u_3 := Function.update u' (tData j) (max (u' (tData j)) (p' (tData j) - 1))
      have hs4 := rStep_move_left A outA
        (q := qWipeS2StepM j) (q' := qWipeS2Check j) (k := tMark j) rfl t_3 p_3 l_3 u_3
      let t_4 := Function.update t_3 (tMark j) ((t_3 (tMark j)).move .left)
      let p_4 := Function.update p_3 (tMark j) (p_3 (tMark j) - 1)
      let l_4 := Function.update l_3 (tMark j) (min (l_3 (tMark j)) (p_3 (tMark j) - 1))
      let u_4 := Function.update u_3 (tMark j) (max (u_3 (tMark j)) (p_3 (tMark j) - 1))
      have hw4 : ∀ r', l_4 r' ≤ p_4 r' ∧ p_4 r' ≤ u_4 r' := by
        intro r'; rcases r' with _ | i | i
        · simp only [p_4, p_3, l_4, l_3, u_4, u_3, Function.update_of_ne (by simp : tIO ≠ tMark j),
            Function.update_of_ne (by simp : tIO ≠ tData j)]; exact hw' tIO
        · by_cases hi : i = j
          · subst i; simp only [p_4, p_3, l_4, l_3, u_4, u_3,
              Function.update_of_ne (by simp : (tData j : RTape A.tapeCount) ≠ tMark j), Function.update_self]
            exact ⟨min_le_right _ _, le_max_right _ _⟩
          · have h1 : (tData i : RTape A.tapeCount) ≠ tData j := fun h => hi (Sum.inl.inj (Sum.inr.inj h))
            simp only [p_4, p_3, l_4, l_3, u_4, u_3,
              Function.update_of_ne (by simp : (tData i : RTape A.tapeCount) ≠ tMark j),
              Function.update_of_ne h1]; exact hw' (tData i)
        · by_cases hi : i = j
          · subst i; simp only [p_4, p_3, l_4, l_3, u_4, u_3, Function.update_self]
            exact ⟨min_le_right _ _, le_max_right _ _⟩
          · have h2 : (tMark i : RTape A.tapeCount) ≠ tMark j := fun h => hi (Sum.inr.inj (Sum.inr.inj h))
            simp only [p_4, p_3, l_4, l_3, u_4, u_3, Function.update_of_ne h2,
              Function.update_of_ne (by simp : (tMark i : RTape A.tapeCount) ≠ tData j)]; exact hw' (tMark i)
      have henv4 : ∀ r', L_env r' ≤ l_4 r' ∧ u_4 r' ≤ U_env r' := by
        intro r'; rcases r' with _ | i | i
        · simp only [l_4, l_3, u_4, u_3, Function.update_of_ne (by simp : tIO ≠ tMark j),
            Function.update_of_ne (by simp : tIO ≠ tData j)]; exact henv' tIO
        · by_cases hi : i = j
          · subst i; have h1 := henv' (tData j)
            change L_env (tData j) ≤ l_4 (tData j) ∧ u_4 (tData j) ≤ U_env (tData j)
            simp only [l_4, u_4, l_3, u_3, Function.update_of_ne (by simp : (tData j : RTape A.tapeCount) ≠ tMark j),
              Function.update_self, hpD']
            exact ⟨le_min h1.1 (by have := hD_env.1; omega), max_le h1.2 (by have := hD_env.2; omega)⟩
          · have h1 : (tData i : RTape A.tapeCount) ≠ tData j := fun h => hi (Sum.inl.inj (Sum.inr.inj h))
            simp only [l_4, l_3, u_4, u_3,
              Function.update_of_ne (by simp : (tData i : RTape A.tapeCount) ≠ tMark j),
              Function.update_of_ne h1]; exact henv' (tData i)
        · by_cases hi : i = j
          · subst i; have h1 := henv' (tMark j)
            change L_env (tMark j) ≤ l_4 (tMark j) ∧ u_4 (tMark j) ≤ U_env (tMark j)
            simp only [l_4, u_4, l_3, u_3, p_3, Function.update_self,
              Function.update_of_ne (by simp : (tMark j : RTape A.tapeCount) ≠ tData j), hpM']
            exact ⟨le_min h1.1 (by have := hM_env.1; omega), max_le h1.2 (by have := hM_env.2; omega)⟩
          · have h2 : (tMark i : RTape A.tapeCount) ≠ tMark j := fun h => hi (Sum.inr.inj (Sum.inr.inj h))
            simp only [l_4, l_3, u_4, u_3, Function.update_of_ne h2,
              Function.update_of_ne (by simp : (tMark i : RTape A.tapeCount) ≠ tData j)]; exact henv' (tMark i)
      have hp4D : p_4 (tData j) = rem' := by simp [p_4, p_3, hpD']; try omega
      have hp4M : p_4 (tMark j) = rem' := by simp [p_4, p_3, hpM']; try omega
      have hD4_eq : ∀ z, absCell (t_4 (tData j)) (rem' : ℤ) z =
          if z = ((rem' + 1 : ℕ) : ℤ) then none else absCell (t' (tData j)) ((rem' + 1 : ℕ) : ℤ) z := by
        intro z
        have heq : t_4 (tData j) = ((t' (tData j)).write none).move .left := by simp [t_4, t_3, t_2, t_1]
        rw [heq, show (rem' : ℤ) = ((rem' + 1 : ℕ) : ℤ) - 1 by omega, absCell_move_left, absCell_write]
      have hM4_eq : ∀ z, absCell (t_4 (tMark j)) (rem' : ℤ) z =
          if z = ((rem' + 1 : ℕ) : ℤ) then none else absCell (t' (tMark j)) ((rem' + 1 : ℕ) : ℤ) z := by
        intro z
        have heq : t_4 (tMark j) = ((t' (tMark j)).write none).move .left := by simp [t_4, t_3, t_2, t_1]
        rw [heq, show (rem' : ℤ) = ((rem' + 1 : ℕ) : ℤ) - 1 by omega, absCell_move_left, absCell_write]
      obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hout1, hp1D, hp1M, hz1, hzL, hmM1, hw1, henv1⟩ :=
        ih t_4 p_4 l_4 u_4 hw4 henv4 hp4D hp4M (by omega)
          (fun z hz => by rw [hD4_eq z]; split_ifs with hzeq; rfl; exact hD_hi' z (by omega))
          (fun z hz => by rw [hD4_eq z]; split_ifs; rfl; exact hD_lo' z hz)
          (fun z => by
            rw [hM4_eq z, hmM' z]
            by_cases hzeq : z = ((rem' + 1 : ℕ) : ℤ)
            · subst z; rw [if_pos rfl, if_neg (by omega), if_neg (by omega)]
            · rw [if_neg hzeq]; split_ifs <;> first | rfl | omega)
      refine ⟨t1, p1, l1, u1, 5 + n1, trace_prepend5 hs0 hs1 hs2 hs3 hs4 htail,
        by omega, ?_, hp1D, hp1M, hz1, hzL, hmM1, hw1, henv1⟩
      intro r hr1 hr2
      have ho := hout1 r hr1 hr2
      have hr' : t_4 r = t' r ∧ p_4 r = p' r ∧ l_4 r = l' r ∧ u_4 r = u' r := by
        dsimp [t_4, t_3, t_2, t_1, p_4, p_3, l_4, l_3, u_4, u_3]
        simp only [Function.update_of_ne hr2, Function.update_of_ne hr1, and_self]
      exact ⟨ho.1.trans hr'.1, ho.2.1.trans hr'.2.1, ho.2.2.1.trans hr'.2.2.1, ho.2.2.2.trans hr'.2.2.2⟩
  exact ind rem t p l u hw henv hpD hpM hrem_le hD_hi hD_lo hmM

private theorem rPhase_wipeS3 (j : Fin A.tapeCount) (L : ℤ)
    (t : RCfg A) (p l u L_env U_env : RPos A)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r) (henv : ∀ r, L_env r ≤ l r ∧ u r ≤ U_env r)
    (hD_env : L_env (tData j) ≤ L - 1 ∧ 0 ≤ U_env (tData j))
    (hM_env : L_env (tMark j) ≤ L - 1 ∧ 0 ≤ U_env (tMark j))
    (hL0 : L ≤ 0)
    (hpeq : p (tMark j) = p (tData j)) (hlo : L - 1 ≤ p (tMark j)) (hhi : p (tMark j) ≤ 0)
    (hmM : ∀ z : ℤ, absCell (t (tMark j)) (p (tMark j)) z =
      if z = 0 then some false else if L ≤ z ∧ z ≤ 0 then some true else none) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (resetMachine A outA)) n
        (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS3Check j)) t p l u)
        (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS4FwdD j)) t1 p1 l1 u1) ∧
      n ≤ 3 * (p (tMark j) - (L - 1)).toNat + 1 ∧
      (∀ r, r ≠ tData j → r ≠ tMark j → t1 r = t r ∧ p1 r = p r ∧ l1 r = l r ∧ u1 r = u r) ∧
      p1 (tData j) = L - 1 ∧ p1 (tMark j) = L - 1 ∧
      (∀ z : ℤ, absCell (t1 (tData j)) (p1 (tData j)) z = absCell (t (tData j)) (p (tData j)) z) ∧
      (∀ z : ℤ, absCell (t1 (tMark j)) (p1 (tMark j)) z = absCell (t (tMark j)) (p (tMark j)) z) ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
  have ind : ∀ (rem : ℕ) (t' : RCfg A) (p' l' u' : RPos A)
      (hw' : ∀ r, l' r ≤ p' r ∧ p' r ≤ u' r) (henv' : ∀ r, L_env r ≤ l' r ∧ u' r ≤ U_env r)
      (hpeq' : p' (tMark j) = p' (tData j)) (hlo' : L - 1 ≤ p' (tMark j)) (hhi' : p' (tMark j) ≤ 0)
      (hrem : (p' (tMark j) - (L - 1)).toNat = rem)
      (hmM' : ∀ z : ℤ, absCell (t' (tMark j)) (p' (tMark j)) z =
        if z = 0 then some false else if L ≤ z ∧ z ≤ 0 then some true else none),
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (resetMachine A outA)) n
          (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS3Check j)) t' p' l' u')
          (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS4FwdD j)) t1 p1 l1 u1) ∧
        n ≤ 3 * rem + 1 ∧
        (∀ r, r ≠ tData j → r ≠ tMark j → t1 r = t' r ∧ p1 r = p' r ∧ l1 r = l' r ∧ u1 r = u' r) ∧
        p1 (tData j) = L - 1 ∧ p1 (tMark j) = L - 1 ∧
        (∀ z : ℤ, absCell (t1 (tData j)) (p1 (tData j)) z = absCell (t' (tData j)) (p' (tData j)) z) ∧
        (∀ z : ℤ, absCell (t1 (tMark j)) (p1 (tMark j)) z = absCell (t' (tMark j)) (p' (tMark j)) z) ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
    intro rem
    induction rem with
    | zero =>
      intro t' p' l' u' hw' henv' hpeq' hlo' hhi' hrem hmM'
      have hpL1 : p' (tMark j) = L - 1 := by omega
      have hhead : (t' (tMark j)).head = none := by
        rw [← absCell_self (t' (tMark j)) (p' (tMark j)), hmM', hpL1]
        split_ifs <;> first | rfl | omega
      have hs := rStep_branch A outA
        (q := qWipeS3Check j) (k := tMark j) rfl t' p' l' u' (hw' (tMark j))
      rw [hhead] at hs
      exact ⟨t', p', l', u', 1, .cons hs (.refl _), le_rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩,
        by omega, hpL1, fun _ => rfl, fun _ => rfl, hw', henv'⟩
    | succ r ih =>
      intro t' p' l' u' hw' henv' hpeq' hlo' hhi' hrem hmM'
      have hp_geL : L ≤ p' (tMark j) := by omega
      have hne : (t' (tMark j)).head ≠ none := by
        rw [← absCell_self (t' (tMark j)) (p' (tMark j)), hmM']
        split_ifs with h0 h1
        · simp
        · simp
        · exact absurd ⟨hp_geL, hhi'⟩ h1
      rcases Option.ne_none_iff_exists'.1 hne with ⟨sym, hhead⟩
      have hs0 := rStep_branch A outA
        (q := qWipeS3Check j) (k := tMark j) rfl t' p' l' u' (hw' (tMark j))
      rw [hhead] at hs0
      have hs1 := rStep_move_left A outA
        (q := qWipeS3StepD j) (q' := qWipeS3StepM j) (k := tData j) rfl t' p' l' u'
      let t_1 := Function.update t' (tData j) ((t' (tData j)).move .left)
      let p_1 := Function.update p' (tData j) (p' (tData j) - 1)
      let l_1 := Function.update l' (tData j) (min (l' (tData j)) (p' (tData j) - 1))
      let u_1 := Function.update u' (tData j) (max (u' (tData j)) (p' (tData j) - 1))
      have hs2 := rStep_move_left A outA
        (q := qWipeS3StepM j) (q' := qWipeS3Check j) (k := tMark j) rfl t_1 p_1 l_1 u_1
      let t_2 := Function.update t_1 (tMark j) ((t_1 (tMark j)).move .left)
      let p_2 := Function.update p_1 (tMark j) (p_1 (tMark j) - 1)
      let l_2 := Function.update l_1 (tMark j) (min (l_1 (tMark j)) (p_1 (tMark j) - 1))
      let u_2 := Function.update u_1 (tMark j) (max (u_1 (tMark j)) (p_1 (tMark j) - 1))
      have hw2 : ∀ r', l_2 r' ≤ p_2 r' ∧ p_2 r' ≤ u_2 r' := by
        intro r'; rcases r' with _ | i | i
        · simp only [p_2, p_1, l_2, l_1, u_2, u_1, Function.update_of_ne (by simp : tIO ≠ tMark j),
            Function.update_of_ne (by simp : tIO ≠ tData j)]; exact hw' tIO
        · by_cases hi : i = j
          · subst i; simp only [p_2, p_1, l_2, l_1, u_2, u_1,
              Function.update_of_ne (by simp : (tData j : RTape A.tapeCount) ≠ tMark j), Function.update_self]
            exact ⟨min_le_right _ _, le_max_right _ _⟩
          · have h1 : (tData i : RTape A.tapeCount) ≠ tData j := fun h => hi (Sum.inl.inj (Sum.inr.inj h))
            simp only [p_2, p_1, l_2, l_1, u_2, u_1,
              Function.update_of_ne (by simp : (tData i : RTape A.tapeCount) ≠ tMark j),
              Function.update_of_ne h1]; exact hw' (tData i)
        · by_cases hi : i = j
          · subst i; simp only [p_2, p_1, l_2, l_1, u_2, u_1, Function.update_self]
            exact ⟨min_le_right _ _, le_max_right _ _⟩
          · have h2 : (tMark i : RTape A.tapeCount) ≠ tMark j := fun h => hi (Sum.inr.inj (Sum.inr.inj h))
            simp only [p_2, p_1, l_2, l_1, u_2, u_1, Function.update_of_ne h2,
              Function.update_of_ne (by simp : (tMark i : RTape A.tapeCount) ≠ tData j)]; exact hw' (tMark i)
      have henv2 : ∀ r', L_env r' ≤ l_2 r' ∧ u_2 r' ≤ U_env r' := by
        intro r'; rcases r' with _ | i | i
        · simp only [l_2, l_1, u_2, u_1, Function.update_of_ne (by simp : tIO ≠ tMark j),
            Function.update_of_ne (by simp : tIO ≠ tData j)]; exact henv' tIO
        · by_cases hi : i = j
          · subst i; have h1 := henv' (tData j)
            change L_env (tData j) ≤ l_2 (tData j) ∧ u_2 (tData j) ≤ U_env (tData j)
            simp only [l_2, u_2, l_1, u_1, Function.update_of_ne (by simp : (tData j : RTape A.tapeCount) ≠ tMark j),
              Function.update_self]
            exact ⟨le_min h1.1 (by have := hD_env.1; omega), max_le h1.2 (by have := hD_env.2; omega)⟩
          · have h1 : (tData i : RTape A.tapeCount) ≠ tData j := fun h => hi (Sum.inl.inj (Sum.inr.inj h))
            simp only [l_2, l_1, u_2, u_1,
              Function.update_of_ne (by simp : (tData i : RTape A.tapeCount) ≠ tMark j),
              Function.update_of_ne h1]; exact henv' (tData i)
        · by_cases hi : i = j
          · subst i; have h1 := henv' (tMark j)
            change L_env (tMark j) ≤ l_2 (tMark j) ∧ u_2 (tMark j) ≤ U_env (tMark j)
            simp only [l_2, u_2, l_1, u_1, p_1, Function.update_self,
              Function.update_of_ne (by simp : (tMark j : RTape A.tapeCount) ≠ tData j)]
            exact ⟨le_min h1.1 (by have := hM_env.1; omega), max_le h1.2 (by have := hM_env.2; omega)⟩
          · have h2 : (tMark i : RTape A.tapeCount) ≠ tMark j := fun h => hi (Sum.inr.inj (Sum.inr.inj h))
            simp only [l_2, l_1, u_2, u_1, Function.update_of_ne h2,
              Function.update_of_ne (by simp : (tMark i : RTape A.tapeCount) ≠ tData j)]; exact henv' (tMark i)
      have hp2M : p_2 (tMark j) = p' (tMark j) - 1 := by simp [p_2, p_1]
      have hmM2 : ∀ z : ℤ, absCell (t_2 (tMark j)) (p_2 (tMark j)) z =
          if z = 0 then some false else if L ≤ z ∧ z ≤ 0 then some true else none := by
        intro z
        have heq : t_2 (tMark j) = (t' (tMark j)).move .left := by simp [t_2, t_1]
        rw [heq, hp2M, absCell_move_left, hmM' z]
      obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hout1, hp1D, hp1M, ht1D, ht1M, hw1, henv1⟩ :=
        ih t_2 p_2 l_2 u_2 hw2 henv2 (by simp [p_2, p_1, hpeq']) (by omega) (by omega) (by omega) hmM2
      refine ⟨t1, p1, l1, u1, 3 + n1, trace_prepend3 hs0 hs1 hs2 htail, by omega, ?_,
        hp1D, hp1M, ?_, ?_, hw1, henv1⟩
      · intro r hr1 hr2
        have ho := hout1 r hr1 hr2
        have hr' : t_2 r = t' r ∧ p_2 r = p' r ∧ l_2 r = l' r ∧ u_2 r = u' r := by
          dsimp [t_2, t_1, p_2, p_1, l_2, l_1, u_2, u_1]
          simp only [Function.update_of_ne hr2, Function.update_of_ne hr1, and_self]
        exact ⟨ho.1.trans hr'.1, ho.2.1.trans hr'.2.1, ho.2.2.1.trans hr'.2.2.1, ho.2.2.2.trans hr'.2.2.2⟩
      · intro z; rw [ht1D z, show t_2 (tData j) = (t' (tData j)).move .left by simp [t_2, t_1],
          show p_2 (tData j) = p' (tData j) - 1 by simp [p_2, p_1], absCell_move_left]
      · intro z; rw [ht1M z, show t_2 (tMark j) = (t' (tMark j)).move .left by simp [t_2, t_1],
          hp2M, absCell_move_left]
  exact ind (p (tMark j) - (L - 1)).toNat t p l u hw henv hpeq hlo hhi rfl hmM

private theorem rPhase_wipeS4 (j : Fin A.tapeCount) (L : ℤ)
    (t : RCfg A) (p l u L_env U_env : RPos A)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r) (henv : ∀ r, L_env r ≤ l r ∧ u r ≤ U_env r)
    (hD_env : L_env (tData j) ≤ L - 1 ∧ 0 ≤ U_env (tData j))
    (hM_env : L_env (tMark j) ≤ L - 1 ∧ 0 ≤ U_env (tMark j))
    (rem : ℕ)
    (hpD : p (tData j) = -(rem : ℤ)) (hpM : p (tMark j) = -(rem : ℤ)) (hrem_le : L ≤ -(rem : ℤ))
    (hD_clean : ∀ z, (z < -(rem : ℤ) ∨ 1 ≤ z) → absCell (t (tData j)) (-(rem : ℤ)) z = none)
    (hmM : ∀ z : ℤ, absCell (t (tMark j)) (-(rem : ℤ)) z =
      if z = 0 then some false else if -(rem : ℤ) ≤ z ∧ z ≤ -1 then some true else none) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (resetMachine A outA)) n
        (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS4Check j)) t p l u)
        (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeClr0D j)) t1 p1 l1 u1) ∧
      n ≤ 5 * rem + 1 ∧
      (∀ r, r ≠ tData j → r ≠ tMark j → t1 r = t r ∧ p1 r = p r ∧ l1 r = l r ∧ u1 r = u r) ∧
      p1 (tData j) = 0 ∧ p1 (tMark j) = 0 ∧
      (∀ z ≠ 0, absCell (t1 (tData j)) 0 z = none ∧ absCell (t1 (tMark j)) 0 z = none) ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
  have ind : ∀ (rem' : ℕ) (t' : RCfg A) (p' l' u' : RPos A)
      (hw' : ∀ r, l' r ≤ p' r ∧ p' r ≤ u' r) (henv' : ∀ r, L_env r ≤ l' r ∧ u' r ≤ U_env r)
      (hpD' : p' (tData j) = -(rem' : ℤ)) (hpM' : p' (tMark j) = -(rem' : ℤ)) (hrem_le' : L ≤ -(rem' : ℤ))
      (hD_clean' : ∀ z, (z < -(rem' : ℤ) ∨ 1 ≤ z) → absCell (t' (tData j)) (-(rem' : ℤ)) z = none)
      (hmM' : ∀ z : ℤ, absCell (t' (tMark j)) (-(rem' : ℤ)) z =
        if z = 0 then some false else if -(rem' : ℤ) ≤ z ∧ z ≤ -1 then some true else none),
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (resetMachine A outA)) n
          (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS4Check j)) t' p' l' u')
          (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeClr0D j)) t1 p1 l1 u1) ∧
        n ≤ 5 * rem' + 1 ∧
        (∀ r, r ≠ tData j → r ≠ tMark j → t1 r = t' r ∧ p1 r = p' r ∧ l1 r = l' r ∧ u1 r = u' r) ∧
        p1 (tData j) = 0 ∧ p1 (tMark j) = 0 ∧
        (∀ z ≠ 0, absCell (t1 (tData j)) 0 z = none ∧ absCell (t1 (tMark j)) 0 z = none) ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
    intro rem'
    induction rem' with
    | zero =>
      intro t' p' l' u' hw' henv' hpD' hpM' _ hD_clean' hmM'
      have hhead : (t' (tMark j)).head = some false := by
        rw [← absCell_self (t' (tMark j)) (p' (tMark j)), hpM', hmM']; simp
      have hs := rStep_branch A outA
        (q := qWipeS4Check j) (k := tMark j) rfl t' p' l' u' (hw' (tMark j))
      rw [hhead] at hs
      exact ⟨t', p', l', u', 1, .cons hs (.refl _), le_rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩,
        by simpa using hpD', by simpa using hpM', fun z hz =>
          ⟨hD_clean' z (by omega), by rw [show (0 : ℤ) = -((0 : ℕ) : ℤ) from rfl, hmM']; split_ifs <;> first | rfl | omega⟩,
        hw', henv'⟩
    | succ rem' ih =>
      intro t' p' l' u' hw' henv' hpD' hpM' hrem_le' hD_clean' hmM'
      have hhead : (t' (tMark j)).head = some true := by
        rw [← absCell_self (t' (tMark j)) (p' (tMark j)), hpM', hmM']
        rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
      have hs0 := rStep_branch A outA
        (q := qWipeS4Check j) (k := tMark j) rfl t' p' l' u' (hw' (tMark j))
      rw [hhead] at hs0
      have hs1 := rStep_write A outA
        (q := qWipeS4ClrD j) (q' := qWipeS4ClrM j) (k := tData j) (sym := none) rfl t' p' l' u' (hw' (tData j))
      let t_1 := Function.update t' (tData j) ((t' (tData j)).write none)
      have hs2 := rStep_write A outA
        (q := qWipeS4ClrM j) (q' := qWipeS4StepD j) (k := tMark j) (sym := none) rfl t_1 p' l' u' (hw' (tMark j))
      let t_2 := Function.update t_1 (tMark j) ((t_1 (tMark j)).write none)
      have hs3 := rStep_move_right A outA
        (q := qWipeS4StepD j) (q' := qWipeS4StepM j) (k := tData j) rfl t_2 p' l' u'
      let t_3 := Function.update t_2 (tData j) ((t_2 (tData j)).move .right)
      let p_3 := Function.update p' (tData j) (p' (tData j) + 1)
      let l_3 := Function.update l' (tData j) (min (l' (tData j)) (p' (tData j) + 1))
      let u_3 := Function.update u' (tData j) (max (u' (tData j)) (p' (tData j) + 1))
      have hs4 := rStep_move_right A outA
        (q := qWipeS4StepM j) (q' := qWipeS4Check j) (k := tMark j) rfl t_3 p_3 l_3 u_3
      let t_4 := Function.update t_3 (tMark j) ((t_3 (tMark j)).move .right)
      let p_4 := Function.update p_3 (tMark j) (p_3 (tMark j) + 1)
      let l_4 := Function.update l_3 (tMark j) (min (l_3 (tMark j)) (p_3 (tMark j) + 1))
      let u_4 := Function.update u_3 (tMark j) (max (u_3 (tMark j)) (p_3 (tMark j) + 1))
      have hw4 : ∀ r', l_4 r' ≤ p_4 r' ∧ p_4 r' ≤ u_4 r' := by
        intro r'; rcases r' with _ | i | i
        · simp only [p_4, p_3, l_4, l_3, u_4, u_3, Function.update_of_ne (by simp : tIO ≠ tMark j),
            Function.update_of_ne (by simp : tIO ≠ tData j)]; exact hw' tIO
        · by_cases hi : i = j
          · subst i; simp only [p_4, p_3, l_4, l_3, u_4, u_3,
              Function.update_of_ne (by simp : (tData j : RTape A.tapeCount) ≠ tMark j), Function.update_self]
            exact ⟨min_le_right _ _, le_max_right _ _⟩
          · have h1 : (tData i : RTape A.tapeCount) ≠ tData j := fun h => hi (Sum.inl.inj (Sum.inr.inj h))
            simp only [p_4, p_3, l_4, l_3, u_4, u_3,
              Function.update_of_ne (by simp : (tData i : RTape A.tapeCount) ≠ tMark j),
              Function.update_of_ne h1]; exact hw' (tData i)
        · by_cases hi : i = j
          · subst i; simp only [p_4, p_3, l_4, l_3, u_4, u_3, Function.update_self]
            exact ⟨min_le_right _ _, le_max_right _ _⟩
          · have h2 : (tMark i : RTape A.tapeCount) ≠ tMark j := fun h => hi (Sum.inr.inj (Sum.inr.inj h))
            simp only [p_4, p_3, l_4, l_3, u_4, u_3, Function.update_of_ne h2,
              Function.update_of_ne (by simp : (tMark i : RTape A.tapeCount) ≠ tData j)]; exact hw' (tMark i)
      have henv4 : ∀ r', L_env r' ≤ l_4 r' ∧ u_4 r' ≤ U_env r' := by
        intro r'; rcases r' with _ | i | i
        · simp only [l_4, l_3, u_4, u_3, Function.update_of_ne (by simp : tIO ≠ tMark j),
            Function.update_of_ne (by simp : tIO ≠ tData j)]; exact henv' tIO
        · by_cases hi : i = j
          · subst i; have h1 := henv' (tData j)
            change L_env (tData j) ≤ l_4 (tData j) ∧ u_4 (tData j) ≤ U_env (tData j)
            simp only [l_4, u_4, l_3, u_3, Function.update_of_ne (by simp : (tData j : RTape A.tapeCount) ≠ tMark j),
              Function.update_self, hpD']
            exact ⟨le_min h1.1 (by have := hD_env.1; omega), max_le h1.2 (by have := hD_env.2; omega)⟩
          · have h1 : (tData i : RTape A.tapeCount) ≠ tData j := fun h => hi (Sum.inl.inj (Sum.inr.inj h))
            simp only [l_4, l_3, u_4, u_3,
              Function.update_of_ne (by simp : (tData i : RTape A.tapeCount) ≠ tMark j),
              Function.update_of_ne h1]; exact henv' (tData i)
        · by_cases hi : i = j
          · subst i; have h1 := henv' (tMark j)
            change L_env (tMark j) ≤ l_4 (tMark j) ∧ u_4 (tMark j) ≤ U_env (tMark j)
            simp only [l_4, u_4, l_3, u_3, p_3, Function.update_self,
              Function.update_of_ne (by simp : (tMark j : RTape A.tapeCount) ≠ tData j), hpM']
            exact ⟨le_min h1.1 (by have := hM_env.1; omega), max_le h1.2 (by have := hM_env.2; omega)⟩
          · have h2 : (tMark i : RTape A.tapeCount) ≠ tMark j := fun h => hi (Sum.inr.inj (Sum.inr.inj h))
            simp only [l_4, l_3, u_4, u_3, Function.update_of_ne h2,
              Function.update_of_ne (by simp : (tMark i : RTape A.tapeCount) ≠ tData j)]; exact henv' (tMark i)
      have hp4D : p_4 (tData j) = -(rem' : ℤ) := by simp [p_4, p_3, hpD']; try omega
      have hp4M : p_4 (tMark j) = -(rem' : ℤ) := by simp [p_4, p_3, hpM']; try omega
      have hD4_eq : ∀ z, absCell (t_4 (tData j)) (-(rem' : ℤ)) z =
          if z = -((rem' + 1 : ℕ) : ℤ) then none else absCell (t' (tData j)) (-((rem' + 1 : ℕ) : ℤ)) z := by
        intro z
        have heq : t_4 (tData j) = ((t' (tData j)).write none).move .right := by simp [t_4, t_3, t_2, t_1]
        rw [heq, show -(rem' : ℤ) = (-((rem' + 1 : ℕ) : ℤ)) + 1 by omega, absCell_move_right, absCell_write]
      have hM4_eq : ∀ z, absCell (t_4 (tMark j)) (-(rem' : ℤ)) z =
          if z = -((rem' + 1 : ℕ) : ℤ) then none else absCell (t' (tMark j)) (-((rem' + 1 : ℕ) : ℤ)) z := by
        intro z
        have heq : t_4 (tMark j) = ((t' (tMark j)).write none).move .right := by simp [t_4, t_3, t_2, t_1]
        rw [heq, show -(rem' : ℤ) = (-((rem' + 1 : ℕ) : ℤ)) + 1 by omega, absCell_move_right, absCell_write]
      obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hout1, hp1D, hp1M, hz1, hw1, henv1⟩ :=
        ih t_4 p_4 l_4 u_4 hw4 henv4 hp4D hp4M (by omega)
          (fun z hz => by rw [hD4_eq z]; split_ifs with hzeq; rfl; exact hD_clean' z (by omega))
          (fun z => by
            rw [hM4_eq z, hmM' z]
            by_cases hzeq : z = -((rem' + 1 : ℕ) : ℤ)
            · subst z; rw [if_pos rfl, if_neg (by omega), if_neg (by omega)]
            · rw [if_neg hzeq]; split_ifs <;> first | rfl | omega)
      refine ⟨t1, p1, l1, u1, 5 + n1, trace_prepend5 hs0 hs1 hs2 hs3 hs4 htail,
        by omega, ?_, hp1D, hp1M, hz1, hw1, henv1⟩
      intro r hr1 hr2
      have ho := hout1 r hr1 hr2
      have hr' : t_4 r = t' r ∧ p_4 r = p' r ∧ l_4 r = l' r ∧ u_4 r = u' r := by
        dsimp [t_4, t_3, t_2, t_1, p_4, p_3, l_4, l_3, u_4, u_3]
        simp only [Function.update_of_ne hr2, Function.update_of_ne hr1, and_self]
      exact ⟨ho.1.trans hr'.1, ho.2.1.trans hr'.2.1, ho.2.2.1.trans hr'.2.2.1, ho.2.2.2.trans hr'.2.2.2⟩
  exact ind rem t p l u hw henv hpD hpM hrem_le hD_clean hmM

private theorem rPhase_wipeOne (j : Fin A.tapeCount) (L U : ℤ)
    (t : RCfg A) (p l u L_env U_env : RPos A)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r) (henv : ∀ r, L_env r ≤ l r ∧ u r ≤ U_env r)
    (hD_env : L_env (tData j) ≤ L - 1 ∧ U + 1 ≤ U_env (tData j))
    (hM_env : L_env (tMark j) ≤ L - 1 ∧ U + 1 ≤ U_env (tMark j))
    (hp_eq : p (tMark j) = p (tData j))
    (hmM : MarkExact (t (tMark j)) (p (tMark j)) L U)
    (hD : DataSupported (t (tData j)) (p (tData j)) L U) :
    let nextQ : RQ A.tapeCount A.stateCount :=
      if h : j.val + 1 < A.tapeCount then qWipeS1Check ⟨j.val + 1, h⟩ else qDone
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (resetMachine A outA)) n
        (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS1Check j)) t p l u)
        (cCfg (rOps A outA) (rStart A) tIO (.inr nextQ) t1 p1 l1 u1) ∧
      n ≤ 11 * (U - L + 2).toNat + 10 ∧
      (∀ r, r ≠ tData j → r ≠ tMark j → t1 r = t r ∧ p1 r = p r ∧ l1 r = l r ∧ u1 r = u r) ∧
      t1 (tData j) = Turing.Tape.mk₁ [] ∧ t1 (tMark j) = Turing.Tape.mk₁ [] ∧
      p1 (tData j) = 0 ∧ p1 (tMark j) = 0 ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
  have hL0 := hmM.1; have h0U := hmM.2.1
  -- Sweep 1: qWipeS1Check j -> qWipeS2BackD j (lands at U + 1)
  obtain ⟨t_s1, p_s1, l_s1, u_s1, n_s1, htr_s1, hn_s1, hout_s1, hp_s1D, hp_s1M, ht_s1D, ht_s1M, hw_s1, henv_s1⟩ :=
    rPhase_wipeS1 A outA j L U t p l u L_env U_env hw henv hD_env hM_env h0U
      hp_eq hmM.2.2.1 (by have := hmM.2.2.2.1; omega) hmM.2.2.2.2
  -- Step back from U + 1 to U: qWipeS2BackD j -> qWipeS2Check j (2 steps)
  have hsb0 := rStep_move_left A outA
    (q := qWipeS2BackD j) (q' := qWipeS2BackM j) (k := tData j) rfl t_s1 p_s1 l_s1 u_s1
  let t_sb1 := Function.update t_s1 (tData j) ((t_s1 (tData j)).move .left)
  let p_sb1 := Function.update p_s1 (tData j) (p_s1 (tData j) - 1)
  let l_sb1 := Function.update l_s1 (tData j) (min (l_s1 (tData j)) (p_s1 (tData j) - 1))
  let u_sb1 := Function.update u_s1 (tData j) (max (u_s1 (tData j)) (p_s1 (tData j) - 1))
  have hsb1 := rStep_move_left A outA
    (q := qWipeS2BackM j) (q' := qWipeS2Check j) (k := tMark j) rfl t_sb1 p_sb1 l_sb1 u_sb1
  let t_s2 := Function.update t_sb1 (tMark j) ((t_sb1 (tMark j)).move .left)
  let p_s2 := Function.update p_sb1 (tMark j) (p_sb1 (tMark j) - 1)
  let l_s2 := Function.update l_sb1 (tMark j) (min (l_sb1 (tMark j)) (p_sb1 (tMark j) - 1))
  let u_s2 := Function.update u_sb1 (tMark j) (max (u_sb1 (tMark j)) (p_sb1 (tMark j) - 1))
  have hps2D : p_s2 (tData j) = U.toNat := by simp [p_s2, p_sb1, hp_s1D]; try omega
  have hps2M : p_s2 (tMark j) = U.toNat := by simp [p_s2, p_sb1, hp_s1M]; try omega
  have hw_s2 : ∀ r, l_s2 r ≤ p_s2 r ∧ p_s2 r ≤ u_s2 r := by
    intro r; rcases r with _ | i | i
    · simp only [p_s2, p_sb1, l_s2, l_sb1, u_s2, u_sb1, Function.update_of_ne (by simp : tIO ≠ tMark j),
        Function.update_of_ne (by simp : tIO ≠ tData j)]; exact hw_s1 tIO
    · by_cases hi : i = j
      · subst i; simp only [p_s2, p_sb1, l_s2, l_sb1, u_s2, u_sb1,
          Function.update_of_ne (by simp : (tData j : RTape A.tapeCount) ≠ tMark j), Function.update_self]
        exact ⟨min_le_right _ _, le_max_right _ _⟩
      · have h1 : (tData i : RTape A.tapeCount) ≠ tData j := fun h => hi (Sum.inl.inj (Sum.inr.inj h))
        simp only [p_s2, p_sb1, l_s2, l_sb1, u_s2, u_sb1,
          Function.update_of_ne (by simp : (tData i : RTape A.tapeCount) ≠ tMark j),
          Function.update_of_ne h1]; exact hw_s1 (tData i)
    · by_cases hi : i = j
      · subst i; simp only [p_s2, p_sb1, l_s2, l_sb1, u_s2, u_sb1, Function.update_self]
        exact ⟨min_le_right _ _, le_max_right _ _⟩
      · have h2 : (tMark i : RTape A.tapeCount) ≠ tMark j := fun h => hi (Sum.inr.inj (Sum.inr.inj h))
        simp only [p_s2, p_sb1, l_s2, l_sb1, u_s2, u_sb1, Function.update_of_ne h2,
          Function.update_of_ne (by simp : (tMark i : RTape A.tapeCount) ≠ tData j)]; exact hw_s1 (tMark i)
  have henv_s2 : ∀ r, L_env r ≤ l_s2 r ∧ u_s2 r ≤ U_env r := by
    intro r; rcases r with _ | i | i
    · simp only [l_s2, l_sb1, u_s2, u_sb1, Function.update_of_ne (by simp : tIO ≠ tMark j),
        Function.update_of_ne (by simp : tIO ≠ tData j)]; exact henv_s1 tIO
    · by_cases hi : i = j
      · subst i; have h1 := henv_s1 (tData j)
        change L_env (tData j) ≤ l_s2 (tData j) ∧ u_s2 (tData j) ≤ U_env (tData j)
        simp only [l_s2, u_s2, l_sb1, u_sb1, Function.update_of_ne (by simp : (tData j : RTape A.tapeCount) ≠ tMark j),
          Function.update_self, hp_s1D]
        exact ⟨le_min h1.1 (by have := hD_env.1; omega), max_le h1.2 (by have := hD_env.2; omega)⟩
      · have h1 : (tData i : RTape A.tapeCount) ≠ tData j := fun h => hi (Sum.inl.inj (Sum.inr.inj h))
        simp only [l_s2, l_sb1, u_s2, u_sb1,
          Function.update_of_ne (by simp : (tData i : RTape A.tapeCount) ≠ tMark j),
          Function.update_of_ne h1]; exact henv_s1 (tData i)
    · by_cases hi : i = j
      · subst i; have h1 := henv_s1 (tMark j)
        change L_env (tMark j) ≤ l_s2 (tMark j) ∧ u_s2 (tMark j) ≤ U_env (tMark j)
        simp only [l_s2, u_s2, l_sb1, u_sb1, p_sb1, Function.update_self,
          Function.update_of_ne (by simp : (tMark j : RTape A.tapeCount) ≠ tData j), hp_s1M]
        exact ⟨le_min h1.1 (by have := hM_env.1; omega), max_le h1.2 (by have := hM_env.2; omega)⟩
      · have h2 : (tMark i : RTape A.tapeCount) ≠ tMark j := fun h => hi (Sum.inr.inj (Sum.inr.inj h))
        simp only [l_s2, l_sb1, u_s2, u_sb1, Function.update_of_ne h2,
          Function.update_of_ne (by simp : (tMark i : RTape A.tapeCount) ≠ tData j)]; exact henv_s1 (tMark i)
  have hD_s2_hi : ∀ z > (U.toNat : ℤ), absCell (t_s2 (tData j)) (U.toNat : ℤ) z = none := by
    intro z hz
    have heq : t_s2 (tData j) = (t_s1 (tData j)).move .left := by simp [t_s2, t_sb1]
    rw [heq, show (U.toNat : ℤ) = (U + 1) - 1 by omega, absCell_move_left, ← hp_s1D, ht_s1D z]
    by_contra hne
    have := (hD z hne).2; omega
  have hD_s2_lo : ∀ z < L, absCell (t_s2 (tData j)) (U.toNat : ℤ) z = none := by
    intro z hz
    have heq : t_s2 (tData j) = (t_s1 (tData j)).move .left := by simp [t_s2, t_sb1]
    rw [heq, show (U.toNat : ℤ) = (U + 1) - 1 by omega, absCell_move_left, ← hp_s1D, ht_s1D z]
    by_contra hne
    have := (hD z hne).1; omega
  have hmM_s2 : ∀ z : ℤ, absCell (t_s2 (tMark j)) (U.toNat : ℤ) z =
      if z = 0 then some false else if L ≤ z ∧ z ≤ (U.toNat : ℤ) then some true else none := by
    intro z
    have heq : t_s2 (tMark j) = (t_s1 (tMark j)).move .left := by simp [t_s2, t_sb1]
    rw [heq, show (U.toNat : ℤ) = (U + 1) - 1 by omega, absCell_move_left, ← hp_s1M, ht_s1M z, hmM.2.2.2.2 z]
    split_ifs <;> first | rfl | omega
  -- Sweep 2: qWipeS2Check j -> qWipeS3Check j
  obtain ⟨t_w2, p_w2, l_w2, u_w2, n_w2, htr_w2, hn_w2, hout_w2, hpw2D, hpw2M, hw2_hi, hw2_lo, hmM_w2, hww2, henv_w2⟩ :=
    rPhase_wipeS2 A outA j L U t_s2 p_s2 l_s2 u_s2 L_env U_env hw_s2 henv_s2 hD_env hM_env hL0
      U.toNat hps2D hps2M (by omega) hD_s2_hi hD_s2_lo hmM_s2
  -- Sweep 3: qWipeS3Check j -> qWipeS4FwdD j
  obtain ⟨t_s3, p_s3, l_s3, u_s3, n_s3, htr_s3, hn_s3, hout_s3, hp_s3D, hp_s3M, ht_s3D, ht_s3M, hw_s3, henv_s3⟩ :=
    rPhase_wipeS3 A outA j L t_w2 p_w2 l_w2 u_w2 L_env U_env hww2 henv_w2
      ⟨hD_env.1, by have := hD_env.2; omega⟩ ⟨hM_env.1, by have := hM_env.2; omega⟩ hL0
      (by rw [hpw2M, hpw2D]) (by rw [hpw2M]; omega) (by rw [hpw2M]) (fun z => by rw [hpw2M]; exact hmM_w2 z)
  -- Step forward from L - 1 to L: qWipeS4FwdD j -> qWipeS4Check j (2 steps)
  have hsf0 := rStep_move_right A outA
    (q := qWipeS4FwdD j) (q' := qWipeS4FwdM j) (k := tData j) rfl t_s3 p_s3 l_s3 u_s3
  let t_sf1 := Function.update t_s3 (tData j) ((t_s3 (tData j)).move .right)
  let p_sf1 := Function.update p_s3 (tData j) (p_s3 (tData j) + 1)
  let l_sf1 := Function.update l_s3 (tData j) (min (l_s3 (tData j)) (p_s3 (tData j) + 1))
  let u_sf1 := Function.update u_s3 (tData j) (max (u_s3 (tData j)) (p_s3 (tData j) + 1))
  have hsf1 := rStep_move_right A outA
    (q := qWipeS4FwdM j) (q' := qWipeS4Check j) (k := tMark j) rfl t_sf1 p_sf1 l_sf1 u_sf1
  let t_s4 := Function.update t_sf1 (tMark j) ((t_sf1 (tMark j)).move .right)
  let p_s4 := Function.update p_sf1 (tMark j) (p_sf1 (tMark j) + 1)
  let l_s4 := Function.update l_sf1 (tMark j) (min (l_sf1 (tMark j)) (p_sf1 (tMark j) + 1))
  let u_s4 := Function.update u_sf1 (tMark j) (max (u_sf1 (tMark j)) (p_sf1 (tMark j) + 1))
  have hw_s4 : ∀ r, l_s4 r ≤ p_s4 r ∧ p_s4 r ≤ u_s4 r := by
    intro r; rcases r with _ | i | i
    · simp only [p_s4, p_sf1, l_s4, l_sf1, u_s4, u_sf1, Function.update_of_ne (by simp : tIO ≠ tMark j),
        Function.update_of_ne (by simp : tIO ≠ tData j)]; exact hw_s3 tIO
    · by_cases hi : i = j
      · subst i; simp only [p_s4, p_sf1, l_s4, l_sf1, u_s4, u_sf1,
          Function.update_of_ne (by simp : (tData j : RTape A.tapeCount) ≠ tMark j), Function.update_self]
        exact ⟨min_le_right _ _, le_max_right _ _⟩
      · have h1 : (tData i : RTape A.tapeCount) ≠ tData j := fun h => hi (Sum.inl.inj (Sum.inr.inj h))
        simp only [p_s4, p_sf1, l_s4, l_sf1, u_s4, u_sf1,
          Function.update_of_ne (by simp : (tData i : RTape A.tapeCount) ≠ tMark j),
          Function.update_of_ne h1]; exact hw_s3 (tData i)
    · by_cases hi : i = j
      · subst i; simp only [p_s4, p_sf1, l_s4, l_sf1, u_s4, u_sf1, Function.update_self]
        exact ⟨min_le_right _ _, le_max_right _ _⟩
      · have h2 : (tMark i : RTape A.tapeCount) ≠ tMark j := fun h => hi (Sum.inr.inj (Sum.inr.inj h))
        simp only [p_s4, p_sf1, l_s4, l_sf1, u_s4, u_sf1, Function.update_of_ne h2,
          Function.update_of_ne (by simp : (tMark i : RTape A.tapeCount) ≠ tData j)]; exact hw_s3 (tMark i)
  have henv_s4 : ∀ r, L_env r ≤ l_s4 r ∧ u_s4 r ≤ U_env r := by
    intro r; rcases r with _ | i | i
    · simp only [l_s4, l_sf1, u_s4, u_sf1, Function.update_of_ne (by simp : tIO ≠ tMark j),
        Function.update_of_ne (by simp : tIO ≠ tData j)]; exact henv_s3 tIO
    · by_cases hi : i = j
      · subst i; have h1 := henv_s3 (tData j)
        change L_env (tData j) ≤ l_s4 (tData j) ∧ u_s4 (tData j) ≤ U_env (tData j)
        simp only [l_s4, u_s4, l_sf1, u_sf1, Function.update_of_ne (by simp : (tData j : RTape A.tapeCount) ≠ tMark j),
          Function.update_self, hp_s3D]
        exact ⟨le_min h1.1 (by have := hD_env.1; omega), max_le h1.2 (by have := hD_env.2; omega)⟩
      · have h1 : (tData i : RTape A.tapeCount) ≠ tData j := fun h => hi (Sum.inl.inj (Sum.inr.inj h))
        simp only [l_s4, l_sf1, u_s4, u_sf1,
          Function.update_of_ne (by simp : (tData i : RTape A.tapeCount) ≠ tMark j),
          Function.update_of_ne h1]; exact henv_s3 (tData i)
    · by_cases hi : i = j
      · subst i; have h1 := henv_s3 (tMark j)
        change L_env (tMark j) ≤ l_s4 (tMark j) ∧ u_s4 (tMark j) ≤ U_env (tMark j)
        simp only [l_s4, u_s4, l_sf1, u_sf1, p_sf1, Function.update_self,
          Function.update_of_ne (by simp : (tMark j : RTape A.tapeCount) ≠ tData j), hp_s3M]
        exact ⟨le_min h1.1 (by have := hM_env.1; omega), max_le h1.2 (by have := hM_env.2; omega)⟩
      · have h2 : (tMark i : RTape A.tapeCount) ≠ tMark j := fun h => hi (Sum.inr.inj (Sum.inr.inj h))
        simp only [l_s4, l_sf1, u_s4, u_sf1, Function.update_of_ne h2,
          Function.update_of_ne (by simp : (tMark i : RTape A.tapeCount) ≠ tData j)]; exact henv_s3 (tMark i)
  have hps4D : p_s4 (tData j) = -((-L).toNat : ℤ) := by simp [p_s4, p_sf1, hp_s3D]; try omega
  have hps4M : p_s4 (tMark j) = -((-L).toNat : ℤ) := by simp [p_s4, p_sf1, hp_s3M]; try omega
  have hD_s4_clean : ∀ z, (z < -((-L).toNat : ℤ) ∨ 1 ≤ z) → absCell (t_s4 (tData j)) (-((-L).toNat : ℤ)) z = none := by
    intro z hz
    have heq : t_s4 (tData j) = (t_s3 (tData j)).move .right := by simp [t_s4, t_sf1]
    rw [heq, show -((-L).toNat : ℤ) = (L - 1) + 1 by omega, absCell_move_right, ← hp_s3D, ht_s3D z, hpw2D]
    rcases hz with hz | hz
    · exact hw2_lo z (by omega)
    · exact (hw2_hi z hz).1
  have hmM_s4 : ∀ z : ℤ, absCell (t_s4 (tMark j)) (-((-L).toNat : ℤ)) z =
      if z = 0 then some false else if -((-L).toNat : ℤ) ≤ z ∧ z ≤ -1 then some true else none := by
    intro z
    have heq : t_s4 (tMark j) = (t_s3 (tMark j)).move .right := by simp [t_s4, t_sf1]
    rw [heq, show -((-L).toNat : ℤ) = (L - 1) + 1 by omega, absCell_move_right, ← hp_s3M, ht_s3M z, hpw2M, hmM_w2 z]
    split_ifs <;> first | rfl | omega
  -- Sweep 4: qWipeS4Check j -> qWipeClr0D j
  obtain ⟨t_w4, p_w4, l_w4, u_w4, n_w4, htr_w4, hn_w4, hout_w4, hpw4D, hpw4M, hw4_clean, hww4, henv_w4⟩ :=
    rPhase_wipeS4 A outA j L t_s4 p_s4 l_s4 u_s4 L_env U_env hw_s4 henv_s4
      ⟨hD_env.1, by have := hD_env.2; omega⟩ ⟨hM_env.1, by have := hM_env.2; omega⟩
      (-L).toNat hps4D hps4M (by omega) hD_s4_clean hmM_s4
  -- Clear cell 0: qWipeClr0D j -> qWipeClr0M j -> nextQ (2 steps)
  let nextQ : RQ A.tapeCount A.stateCount :=
    if h : j.val + 1 < A.tapeCount then qWipeS1Check ⟨j.val + 1, h⟩ else qDone
  have hc0 := rStep_write A outA
    (q := qWipeClr0D j) (q' := qWipeClr0M j) (k := tData j) (sym := none) rfl t_w4 p_w4 l_w4 u_w4 (hww4 (tData j))
  let t_f1 := Function.update t_w4 (tData j) ((t_w4 (tData j)).write none)
  have hc1 := rStep_write A outA
    (q := qWipeClr0M j) (q' := nextQ) (k := tMark j) (sym := none) rfl t_f1 p_w4 l_w4 u_w4 (hww4 (tMark j))
  let t_f := Function.update t_f1 (tMark j) ((t_f1 (tMark j)).write none)
  have ht_f_D : t_f (tData j) = Turing.Tape.mk₁ [] := by
    apply (blank_iff_absCell (p := (0 : ℤ))).1
    intro z
    have heq : t_f (tData j) = (t_w4 (tData j)).write none := by simp [t_f, t_f1]
    rw [heq, absCell_write]
    by_cases hz : z = 0
    · simp [hz]
    · rw [if_neg hz]; exact (hw4_clean z hz).1
  have ht_f_M : t_f (tMark j) = Turing.Tape.mk₁ [] := by
    apply (blank_iff_absCell (p := (0 : ℤ))).1
    intro z
    have heq : t_f (tMark j) = (t_w4 (tMark j)).write none := by simp [t_f, t_f1]
    rw [heq, absCell_write]
    by_cases hz : z = 0
    · simp [hz]
    · rw [if_neg hz]; exact (hw4_clean z hz).2
  have htr_tot := Trace.append htr_s1
    (Trace.append (.cons hsb0 (.cons hsb1 (.refl _)))
      (Trace.append htr_w2 (Trace.append htr_s3
        (Trace.append (.cons hsf0 (.cons hsf1 (.refl _)))
          (Trace.append htr_w4 (.cons hc0 (.cons hc1 (.refl _))))))))
  refine ⟨t_f, p_w4, l_w4, u_w4, n_s1 + (2 + (n_w2 + (n_s3 + (2 + (n_w4 + 2))))), htr_tot, ?_, ?_,
    ht_f_D, ht_f_M, hpw4D, hpw4M, hww4, henv_w4⟩
  · rw [hpw2M] at hn_s3
    have := hL0; have := h0U; have := hmM.2.2.1; have := hmM.2.2.2.1; omega
  · intro r hr1 hr2
    have h4 := hout_w4 r hr1 hr2
    have h3 := hout_s3 r hr1 hr2
    have h2 := hout_w2 r hr1 hr2
    have h1 := hout_s1 r hr1 hr2
    have htf : t_f r = t_w4 r := by simp [t_f, t_f1, hr1, hr2]
    have hsf : t_s4 r = t_s3 r ∧ p_s4 r = p_s3 r ∧ l_s4 r = l_s3 r ∧ u_s4 r = u_s3 r := by
      dsimp [t_s4, t_sf1, p_s4, p_sf1, l_s4, l_sf1, u_s4, u_sf1]
      simp only [Function.update_of_ne hr2, Function.update_of_ne hr1, and_self]
    have hsb : t_s2 r = t_s1 r ∧ p_s2 r = p_s1 r ∧ l_s2 r = l_s1 r ∧ u_s2 r = u_s1 r := by
      dsimp [t_s2, t_sb1, p_s2, p_sb1, l_s2, l_sb1, u_s2, u_sb1]
      simp only [Function.update_of_ne hr2, Function.update_of_ne hr1, and_self]
    exact ⟨htf.trans (h4.1.trans (hsf.1.trans (h3.1.trans (h2.1.trans (hsb.1.trans h1.1))))),
           h4.2.1.trans (hsf.2.1.trans (h3.2.1.trans (h2.2.1.trans (hsb.2.1.trans h1.2.1)))),
           h4.2.2.1.trans (hsf.2.2.1.trans (h3.2.2.1.trans (h2.2.2.1.trans (hsb.2.2.1.trans h1.2.2.1)))),
           h4.2.2.2.trans (hsf.2.2.2.trans (h3.2.2.2.trans (h2.2.2.2.trans (hsb.2.2.2.trans h1.2.2.2))))⟩

private theorem rPhase_wipeAll (L U : Fin A.tapeCount → ℤ)
    (t : RCfg A) (p l u L_env U_env : RPos A)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r) (henv : ∀ r, L_env r ≤ l r ∧ u r ≤ U_env r)
    (hLU_env : ∀ j, L_env (tData j) ≤ L j - 1 ∧ U j + 1 ≤ U_env (tData j) ∧
                    L_env (tMark j) ≤ L j - 1 ∧ U j + 1 ≤ U_env (tMark j))
    (hp_eq : ∀ j, p (tMark j) = p (tData j))
    (hmM : ∀ j, MarkExact (t (tMark j)) (p (tMark j)) (L j) (U j))
    (hD : ∀ j, DataSupported (t (tData j)) (p (tData j)) (L j) (U j)) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (resetMachine A outA)) n
        (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS1Check ⟨0, Fin.pos A.inputTape⟩)) t p l u)
        (cCfg (rOps A outA) (rStart A) tIO (.inl true) t1 p1 l1 u1) ∧
      n ≤ ∑ j : Fin A.tapeCount, (11 * (U j - L j + 2).toNat + 10) + 1 ∧
      t1 tIO = t tIO ∧ p1 tIO = p tIO ∧
      (∀ j, t1 (tData j) = Turing.Tape.mk₁ [] ∧ t1 (tMark j) = Turing.Tape.mk₁ [] ∧
            p1 (tData j) = 0 ∧ p1 (tMark j) = 0) ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
  have ind : ∀ (rem k : ℕ) (hk : k < A.tapeCount) (hrem : A.tapeCount - k = rem)
      (t' : RCfg A) (p' l' u' : RPos A)
      (hw' : ∀ r, l' r ≤ p' r ∧ p' r ≤ u' r) (henv' : ∀ r, L_env r ≤ l' r ∧ u' r ≤ U_env r)
      (hio : t' tIO = t tIO ∧ p' tIO = p tIO)
      (hlt_clean : ∀ j : Fin A.tapeCount, j.val < k →
        t' (tData j) = Turing.Tape.mk₁ [] ∧ t' (tMark j) = Turing.Tape.mk₁ [] ∧
        p' (tData j) = 0 ∧ p' (tMark j) = 0)
      (hge_inv : ∀ j : Fin A.tapeCount, k ≤ j.val →
        p' (tMark j) = p' (tData j) ∧ MarkExact (t' (tMark j)) (p' (tMark j)) (L j) (U j) ∧
        DataSupported (t' (tData j)) (p' (tData j)) (L j) (U j)),
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (resetMachine A outA)) n
          (cCfg (rOps A outA) (rStart A) tIO (.inr (qWipeS1Check ⟨k, hk⟩)) t' p' l' u')
          (cCfg (rOps A outA) (rStart A) tIO (.inl true) t1 p1 l1 u1) ∧
        n ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin A.tapeCount => k ≤ j.val),
              (11 * (U j - L j + 2).toNat + 10) + 1 ∧
        t1 tIO = t tIO ∧ p1 tIO = p tIO ∧
        (∀ j, t1 (tData j) = Turing.Tape.mk₁ [] ∧ t1 (tMark j) = Turing.Tape.mk₁ [] ∧
              p1 (tData j) = 0 ∧ p1 (tMark j) = 0) ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env r ≤ l1 r ∧ u1 r ≤ U_env r) := by
    intro rem
    induction rem with
    | zero => intro k hk hrem; omega
    | succ r ih =>
      intro k hk hrem t' p' l' u' hw' henv' hio hlt_clean hge_inv
      let jk : Fin A.tapeCount := ⟨k, hk⟩
      have hinvk := hge_inv jk le_rfl
      have hlu_k := hLU_env jk
      obtain ⟨t_w, p_w, l_w, u_w, n_w, htr_w, hn_w, hout_w, hD_w, hM_w, hpD_w, hpM_w, hw_w, henv_w⟩ :=
        rPhase_wipeOne A outA jk (L jk) (U jk) t' p' l' u' L_env U_env hw' henv'
          ⟨hlu_k.1, hlu_k.2.1⟩ ⟨hlu_k.2.2.1, hlu_k.2.2.2⟩ hinvk.1 hinvk.2.1 hinvk.2.2
      have hio_w : t_w tIO = t tIO ∧ p_w tIO = p tIO := by
        have := hout_w tIO (by simp) (by simp)
        exact ⟨this.1.trans hio.1, this.2.1.trans hio.2⟩
      by_cases hlt : k + 1 < A.tapeCount
      · have hnext : ((if h : jk.val + 1 < A.tapeCount then qWipeS1Check ⟨jk.val + 1, h⟩ else qDone) :
            RQ A.tapeCount A.stateCount) = qWipeS1Check ⟨k + 1, hlt⟩ := by simp [jk, hlt]
        rw [hnext] at htr_w
        have hlt_clean' : ∀ j : Fin A.tapeCount, j.val < k + 1 →
            t_w (tData j) = Turing.Tape.mk₁ [] ∧ t_w (tMark j) = Turing.Tape.mk₁ [] ∧
            p_w (tData j) = 0 ∧ p_w (tMark j) = 0 := by
          intro j hj
          by_cases hjk : j.val = k
          · have hjk' : j = jk := Fin.ext hjk; subst j; exact ⟨hD_w, hM_w, hpD_w, hpM_w⟩
          · have hne1 : (tData j : RTape A.tapeCount) ≠ tData jk := by
              intro h; exact hjk (congrArg Fin.val (Sum.inl.inj (Sum.inr.inj h)))
            have hne2 : (tMark j : RTape A.tapeCount) ≠ tMark jk := by
              intro h; exact hjk (congrArg Fin.val (Sum.inr.inj (Sum.inr.inj h)))
            have h1 := hout_w (tData j) hne1 (by simp)
            have h2 := hout_w (tMark j) (by simp) hne2
            have hc := hlt_clean j (by omega)
            exact ⟨h1.1.trans hc.1, h2.1.trans hc.2.1, h1.2.1.trans hc.2.2.1, h2.2.1.trans hc.2.2.2⟩
        have hge_inv' : ∀ j : Fin A.tapeCount, k + 1 ≤ j.val →
            p_w (tMark j) = p_w (tData j) ∧ MarkExact (t_w (tMark j)) (p_w (tMark j)) (L j) (U j) ∧
            DataSupported (t_w (tData j)) (p_w (tData j)) (L j) (U j) := by
          intro j hj
          have hne_d : (tData j : RTape A.tapeCount) ≠ tData jk := by
            intro h; have hval := congrArg Fin.val (Sum.inl.inj (Sum.inr.inj h)); dsimp [jk] at hval; omega
          have hne_m : (tMark j : RTape A.tapeCount) ≠ tMark jk := by
            intro h; have hval := congrArg Fin.val (Sum.inr.inj (Sum.inr.inj h)); dsimp [jk] at hval; omega
          have h1 := hout_w (tData j) hne_d (by simp)
          have h2 := hout_w (tMark j) (by simp) hne_m
          have hi := hge_inv j (by omega)
          rw [h2.2.1, h1.2.1, h2.1, h1.1]; exact hi
        obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hio1, hp1, hclean1, hw1, henv1⟩ :=
          ih (k + 1) hlt (by omega) t_w p_w l_w u_w hw_w henv_w hio_w hlt_clean' hge_inv'
        have hsplit : Finset.univ.filter (fun j : Fin A.tapeCount => k ≤ j.val) =
            insert jk (Finset.univ.filter (fun j : Fin A.tapeCount => k + 1 ≤ j.val)) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, jk]
          exact ⟨fun h => by by_cases hjk : j = ⟨k, hk⟩; exact .inl hjk; exact .inr (by have : j.val ≠ k := fun hv => hjk (Fin.ext hv); omega),
                 fun h => by rcases h with rfl | h <;> [exact le_rfl; exact by omega]⟩
        have hnotmem : jk ∉ Finset.univ.filter (fun j : Fin A.tapeCount => k + 1 ≤ j.val) := by
          simp [jk]
        have hsum : ∑ j ∈ Finset.univ.filter (fun j : Fin A.tapeCount => k ≤ j.val),
              (11 * (U j - L j + 2).toNat + 10) =
            (11 * (U jk - L jk + 2).toNat + 10) +
              ∑ j ∈ Finset.univ.filter (fun j : Fin A.tapeCount => k + 1 ≤ j.val),
                (11 * (U j - L j + 2).toNat + 10) := by
          rw [hsplit, Finset.sum_insert hnotmem]
        refine ⟨t1, p1, l1, u1, n_w + n1, Trace.append htr_w htail, by omega, hio1, hp1, hclean1, hw1, henv1⟩
      · have hnext : ((if h : jk.val + 1 < A.tapeCount then qWipeS1Check ⟨jk.val + 1, h⟩ else qDone) :
            RQ A.tapeCount A.stateCount) = qDone := by simp [jk, hlt]
        rw [hnext] at htr_w
        have hhalt := rStep_halt A outA (q := qDone) rfl t_w p_w l_w u_w
        have hclean1 : ∀ j : Fin A.tapeCount,
            t_w (tData j) = Turing.Tape.mk₁ [] ∧ t_w (tMark j) = Turing.Tape.mk₁ [] ∧
            p_w (tData j) = 0 ∧ p_w (tMark j) = 0 := by
          intro j
          by_cases hjk : j.val = k
          · have hjk' : j = jk := Fin.ext hjk; subst j; exact ⟨hD_w, hM_w, hpD_w, hpM_w⟩
          · have hjlt : j.val < k := by omega
            have hne1 : (tData j : RTape A.tapeCount) ≠ tData jk := by
              intro h; exact hjk (congrArg Fin.val (Sum.inl.inj (Sum.inr.inj h)))
            have hne2 : (tMark j : RTape A.tapeCount) ≠ tMark jk := by
              intro h; exact hjk (congrArg Fin.val (Sum.inr.inj (Sum.inr.inj h)))
            have h1 := hout_w (tData j) hne1 (by simp)
            have h2 := hout_w (tMark j) (by simp) hne2
            have hc := hlt_clean j hjlt
            exact ⟨h1.1.trans hc.1, h2.1.trans hc.2.1, h1.2.1.trans hc.2.2.1, h2.2.1.trans hc.2.2.2⟩
        have hsingle : 11 * (U jk - L jk + 2).toNat + 10 ≤
            ∑ j ∈ Finset.univ.filter (fun j : Fin A.tapeCount => k ≤ j.val),
              (11 * (U j - L j + 2).toNat + 10) :=
          Finset.single_le_sum (f := fun j => 11 * (U j - L j + 2).toNat + 10)
            (fun _ _ => Nat.zero_le _) (by simp [jk])
        exact ⟨t_w, p_w, l_w, u_w, n_w + 1, Trace.append htr_w (.cons hhalt (.refl _)), by omega,
          hio_w.1, hio_w.2, hclean1, hw_w, henv_w⟩
  obtain ⟨t1, p1, l1, u1, n, htr, hn, hio, hp, hclean, hw1, henv1⟩ :=
    ind A.tapeCount 0 (Fin.pos A.inputTape) (Nat.sub_zero _) t p l u hw henv ⟨rfl, rfl⟩
      (fun j hj => by omega) (fun j _ => ⟨hp_eq j, hmM j, hD j⟩)
  refine ⟨t1, p1, l1, u1, n, htr, ?_, hio, hp, hclean, hw1, henv1⟩
  simpa using hn

end Phases

end ResetBlock

end DetDLP.M89Resettable

open DetDLP DetDLP.MachineComposition DetDLP.M89Resettable
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Top-level witness for `DetDLP.m89_resettable_machine`. -/
theorem solution (A : PrimitiveMachine) (outA : Fin A.tapeCount) :
    ∃ (R : PrimitiveMachine) (C : ℕ),
      1 ≤ C ∧
      ∀ (input output : List Bool) (τ σ : ℝ), 0 ≤ τ → 0 ≤ σ →
        RunsWithin A outA input output τ σ →
        ∃ (n B : ℕ) (final : LocatedCfg R),
          Computation.Trace (locatedStep R) n (locatedInit R input) final ∧
          (∃ b : Bool, final.config.state = .inl b) ∧
          final.config.tapes R.inputTape = Turing.Tape.mk₁ (output.map some) ∧
          (∀ j : Fin R.tapeCount, j ≠ R.inputTape → final.config.tapes j = Turing.Tape.mk₁ []) ∧
          (∀ j : Fin R.tapeCount, final.position j = 0) ∧
          (n : ℝ) ≤ (C : ℝ) * (τ + σ + 1) ∧
          (B : ℝ) ≤ (C : ℝ) * (σ + 1) ∧
          (∀ j : Fin R.tapeCount, -(B : ℤ) ≤ final.lower j ∧ final.upper j ≤ (B : ℤ)) := by
  let R := resetMachine A outA
  let C : ℕ := 45 * A.tapeCount + 45
  refine ⟨R, C, by dsimp [C]; omega, ?_⟩
  intro input output τ σ hτ hσ hA
  have hin_len := runsWithin_input_length_le hA
  have hout_len := runsWithin_output_length_le hA
  rcases hA with ⟨steps, dA, htrA, ⟨bAns, hdA⟩, hdA_out, hsteps_le, hsp_le⟩
  have hwA : LocatedWellFormed dA := locatedWellFormed_trace (locatedWellFormed_init A input) htrA
  have hsupA : TapeSupportBound dA := tapeSupportBound_trace htrA
  have hcovA : OriginCovered dA := originCovered_trace (originCovered_init A input) htrA
  have hsp_dA' : (visitedSpace dA : ℝ) ≤ σ := hsp_le steps dA le_rfl htrA
  let S_int : ℕ := visitedSpace dA
  have hS_real : (S_int : ℝ) ≤ σ := hsp_dA'
  have hdA_bounds : ∀ j : Fin A.tapeCount,
      -(S_int : ℤ) ≤ dA.lower j ∧ dA.upper j ≤ (S_int : ℤ) := by
    intro j
    have hj_term : (dA.upper j - dA.lower j + 1).toNat ≤ S_int :=
      Finset.single_le_sum (f := fun i => (dA.upper i - dA.lower i + 1).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hc := hcovA j
    omega
  let B : ℕ := S_int + max input.length output.length + 4
  let L_env : RPos A := fun _ => -(B : ℤ)
  let U_env : RPos A := fun _ => (B : ℤ)
  -- Initial cCfg equals locatedInit R input!
  let t0 : RCfg A := fun r => match r with
    | .inl () => Turing.Tape.mk₁ (input.map some)
    | _ => Turing.Tape.mk₁ []
  let p0 : RPos A := fun _ => 0
  let l0 : RPos A := fun _ => 0
  let u0 : RPos A := fun r => match r with
    | .inl () => Int.ofNat (input.length - 1)
    | _ => 0
  have hinit_eq : locatedInit R input = cCfg (rOps A outA) (rStart A) tIO (.inr (rStart A)) t0 p0 l0 u0 := by
    apply loc_ext
    · rfl
    · intro i
      obtain ⟨r, rfl⟩ := (Fintype.equivFin (RTape A.tapeCount)).surjective i
      rcases r with _ | j | j <;> simp [locatedInit, PrimitiveMachine.init, R, resetMachine, cMachine, cCfg, t0, tIO]
    · intro i
      obtain ⟨r, rfl⟩ := (Fintype.equivFin (RTape A.tapeCount)).surjective i
      rcases r with _ | j | j <;> simp [locatedInit, cCfg, p0]
    · intro i
      obtain ⟨r, rfl⟩ := (Fintype.equivFin (RTape A.tapeCount)).surjective i
      rcases r with _ | j | j <;> simp [locatedInit, cCfg, l0]
    · intro i
      obtain ⟨r, rfl⟩ := (Fintype.equivFin (RTape A.tapeCount)).surjective i
      rcases r with _ | j | j <;> simp [locatedInit, R, resetMachine, cMachine, cCfg, u0, tIO]
  have hw0 : ∀ r, l0 r ≤ p0 r ∧ p0 r ≤ u0 r := by
    intro r; rcases r with _ | j | j <;> simp [l0, p0, u0]
  have henv0 : ∀ r, L_env r ≤ l0 r ∧ u0 r ≤ U_env r := by
    intro r; rcases r with _ | j | j <;> simp [L_env, U_env, l0, u0]; dsimp [B]; omega
  -- Phase 1: markZero
  obtain ⟨t1, n1, htr1, hn1, ht1_io, ht1_D, ht1_M⟩ :=
    rPhase_markZero A outA t0 p0 l0 u0 hw0 (fun j => ⟨rfl, rfl⟩)
  -- Phase 2: copyIn
  have ht1_io_eq : t1 tIO = Turing.Tape.mk₁ (input.map some) := ht1_io
  have ht1_io_word : IsWordAt (t1 tIO) 0 input := (isWordAt_zero_iff (t1 tIO) input).2 ht1_io_eq
  obtain ⟨t2, p2, l2, u2, n2, htr2, hn2, hout2, _, hp2io, hp2D, hp2M, hw2, henv2, ht2D, ht2M⟩ :=
    rPhase_copyIn A outA input t1 p0 l0 u0 L_env U_env hw0 henv0
      ⟨by dsimp [L_env, B]; omega, by dsimp [U_env, B]; omega,
       by dsimp [L_env, B]; omega, by dsimp [U_env, B]; omega,
       by dsimp [L_env, B]; omega, by dsimp [U_env, B]; omega⟩
      rfl rfl rfl ht1_io_word (ht1_D A.inputTape) (ht1_M A.inputTape)
  -- Phase 3: eraseIO
  obtain ⟨t3, p3, l3, u3, n3, htr3, hn3, hout3, ht3io, hp3io, hw3, henv3⟩ :=
    rPhase_eraseIO A outA input.length t2 p2 l2 u2 L_env U_env hw2 henv2
      (by dsimp [L_env, B]; omega) hp2io
      (fun z => by
        rw [‹IsWordAt (t2 tIO) (input.length : ℤ) input› z]
        split_ifs with h <;> simp [h] <;> omega)
  -- Phase 4: rewD
  obtain ⟨t4, p4, l4, u4, n4, htr4, hn4, hout4, ht4D_cells, hp4D, hw4, henv4⟩ :=
    rPhase_rewindLeft A outA qRewDStart qRewDCheck qRewDRight qRewMStart (tData A.inputTape)
      input.length rfl rfl rfl t3 p3 l3 u3 L_env U_env hw3 henv3
      (by dsimp [L_env, B]; omega) (by rw [(hout3 _ (by simp)).2.1, hp2D])
      (by rw [(hout3 _ (by simp)).1, ht2D (-1), dif_neg (by omega)])
      (fun z hz0 hzl => by rw [(hout3 _ (by simp)).1, ht2D z, dif_pos ⟨hz0, by omega⟩]; simp)
  -- Phase 5: rewM
  obtain ⟨t5, p5, l5, u5, n5, htr5, hn5, hout5, ht5M_cells, hp5M, hw5, henv5⟩ :=
    rPhase_rewindLeft A outA qRewMStart qRewMCheck qRewMRight (qSim A.start) (tMark A.inputTape)
      input.length rfl rfl rfl t4 p4 l4 u4 L_env U_env hw4 henv4
      (by dsimp [L_env, B]; omega)
      (by rw [(hout4 _ (by simp)).2.1, (hout3 _ (by simp)).2.1, hp2M])
      (by rw [(hout4 _ (by simp)).1, (hout3 _ (by simp)).1, ht2M (-1), if_neg (by omega), if_neg (by omega)])
      (fun z hz0 hzl => by
        rw [(hout4 _ (by simp)).1, (hout3 _ (by simp)).1, ht2M z]
        split_ifs <;> simp_all; omega)
  -- Check state at Phase 6 entry (`locatedInit A input`):
  have hD_sim_in : ∀ j, t5 (tData j) = (locatedInit A input).config.tapes j ∧ p5 (tData j) = (locatedInit A input).position j := by
    intro j
    by_cases hj : j = A.inputTape
    · subst j
      have hword : t5 (tData A.inputTape) = Turing.Tape.mk₁ (input.map some) := by
        apply (isWordAt_zero_iff _ _).1
        intro z
        rw [(hout5 _ (by simp)).1, ht4D_cells z, (hout3 _ (by simp)).1, ht2D z]
      refine ⟨?_, ?_⟩
      · simp [locatedInit, PrimitiveMachine.init, hword]
      · rw [(hout5 _ (by simp)).2.1, hp4D]; rfl
    · have h5 := hout5 (tData j) (by simp)
      have h4 := hout4 (tData j) (by intro h; exact hj (Sum.inl.inj (Sum.inr.inj h)))
      have h3 := hout3 (tData j) (by simp)
      have h2 := hout2 (tData j) (by simp) (by intro h; exact hj (Sum.inl.inj (Sum.inr.inj h))) (by simp)
      rw [h5.1, h4.1, h3.1, h2.1, ht1_D j, h5.2.1, h4.2.1, h3.2.1, h2.2.1]
      simp [locatedInit, PrimitiveMachine.init, hj, t0, p0]
  have hM_sim_in : ∀ j, p5 (tMark j) = (locatedInit A input).position j ∧
      MarkExact (t5 (tMark j)) (p5 (tMark j)) ((locatedInit A input).lower j) ((locatedInit A input).upper j) := by
    intro j
    by_cases hj : j = A.inputTape
    · subst j
      refine ⟨hp5M, ?_⟩
      rw [hp5M]
      refine ⟨le_rfl, by simp [locatedInit], le_rfl, by simp [locatedInit], ?_⟩
      intro z
      rw [ht5M_cells z, (hout4 _ (by simp)).1, (hout3 _ (by simp)).1, ht2M z]
      simp only [locatedInit, ↓reduceIte, Int.ofNat_eq_natCast]
      by_cases h0 : z = 0
      · simp [h0]
      · rw [if_neg h0, if_neg h0]; split_ifs <;> first | rfl | omega
    · have h5 := hout5 (tMark j) (by intro h; exact hj (Sum.inr.inj (Sum.inr.inj h)))
      have h4 := hout4 (tMark j) (by simp)
      have h3 := hout3 (tMark j) (by simp)
      have h2 := hout2 (tMark j) (by simp) (by simp) (by intro h; exact hj (Sum.inr.inj (Sum.inr.inj h)))
      have hp5j : p5 (tMark j) = 0 := by rw [h5.2.1, h4.2.1, h3.2.1, h2.2.1]
      refine ⟨hp5j, ?_⟩
      rw [hp5j]
      refine ⟨le_rfl, by simp [locatedInit, hj], le_rfl, by simp [locatedInit, hj], ?_⟩
      intro z
      rw [h5.1, h4.1, h3.1, h2.1, ht1_M j, absCell_write]
      simp only [locatedInit, hj, ↓reduceIte]
      by_cases hz : z = 0
      · subst hz; simp
      · rw [if_neg hz, if_neg hz, if_neg (by omega)]; dsimp [t0]; rw [absCell, sub_zero, nth_mk₁_nil]
  -- Phase 6: rPhase_sim
  obtain ⟨t6, p6, l6, u6, n6, htr6, hn6, ht6io, hp6io, hl6io, hu6io, hD6, hM6, hw6, henv6⟩ :=
    rPhase_sim A outA steps htrA bAns hdA t5 p5 l5 u5 L_env U_env rfl hw5 henv5
      (locatedWellFormed_init A input) (tapeSupportBound_init A input) hD_sim_in hM_sim_in
      (fun j => ⟨by dsimp [L_env, B]; have := (hdA_bounds j).1; omega,
                 by dsimp [U_env, B]; have := (hdA_bounds j).2; omega,
                 by dsimp [L_env, B]; have := (hdA_bounds j).1; omega,
                 by dsimp [U_env, B]; have := (hdA_bounds j).2; omega⟩)
  -- Check phase 6 output tape `.io` still blank and at 0
  have ht5_io : t5 tIO = Turing.Tape.mk₁ [] ∧ p5 tIO = 0 := by
    have h5 := hout5 tIO (by simp)
    have h4 := hout4 tIO (by simp)
    exact ⟨h5.1.trans (h4.1.trans ht3io), h5.2.1.trans (h4.2.1.trans hp3io)⟩
  have hD6_out_cells : ∀ z : ℤ, absCell (t6 (tData outA)) (dA.position outA) z =
      if h : dA.position outA ≤ z ∧ (z - dA.position outA).toNat < output.length
      then some output[(z - dA.position outA).toNat] else none := by
    intro z
    rw [(hD6 outA).1, absCell, hdA_out]
    have h := absCell_mk₁_zero output (z - dA.position outA)
    simp only [absCell, sub_zero] at h
    rw [h]
    by_cases hp : dA.position outA ≤ z
    · simp [hp]
    · simp [hp]
  have hsup6_out : ∀ k < output.length, dA.lower outA ≤ dA.position outA + k ∧ dA.position outA + k ≤ dA.upper outA := by
    intro k hk
    apply hsupA outA (dA.position outA + k)
    rw [absCell, add_sub_cancel_left, hdA_out, nth_tape_mk₁_get hk]
    simp
  -- Phase 7: outRead
  obtain ⟨t7, p7, l7, u7, n7, htr7, hn7, hout7, ht7_io, hp7_io, hp7_D, hp7_M, hmM7_out, hD7_out, hw7, henv7⟩ :=
    rPhase_outRead A outA output (dA.position outA) (dA.lower outA) (dA.upper outA)
      t6 p6 l6 u6 L_env U_env hw6 henv6
      ⟨by dsimp [L_env, B]; omega, by dsimp [U_env, B]; omega⟩
      ⟨by dsimp [L_env, B]; have := (hdA_bounds outA).1; omega,
       by dsimp [U_env, B]; have := (hdA_bounds outA).2; omega⟩
      ⟨by dsimp [L_env, B]; have := (hdA_bounds outA).1; omega,
       by dsimp [U_env, B]; have := (hdA_bounds outA).2; omega⟩
      (hp6io.trans ht5_io.2) ((isWordAt_zero_iff _ _).2 (ht6io.trans ht5_io.1))
      (hD6 outA).2 hD6_out_cells (hM6 outA).1 ((hM6 outA).1 ▸ (hM6 outA).2) hsup6_out
  -- Phase 8: rewIO
  obtain ⟨t8, p8, l8, u8, n8, htr8, hn8, hout8, ht8_io_cells, hp8_io, hw8, henv8⟩ :=
    rPhase_rewindLeft A outA qRewIOStart qRewIOCheck qRewIORight (qWipeS1Check ⟨0, Fin.pos A.inputTape⟩)
      tIO output.length rfl rfl rfl t7 p7 l7 u7 L_env U_env hw7 henv7
      (by dsimp [L_env, B]; omega) hp7_io
      (by rw [ht7_io (-1), dif_neg (by omega)])
      (fun z hz0 hzl => by rw [ht7_io z, dif_pos ⟨hz0, by omega⟩]; simp)
  have ht8_io_eq : t8 tIO = Turing.Tape.mk₁ (output.map some) := by
    apply (isWordAt_zero_iff _ _).1
    intro z; rw [ht8_io_cells z, ht7_io z]
  -- Prepare wipe bounds: L j = dA.lower j, U j = if j = outA then max (dA.upper outA) (dA.position outA + output.length) else dA.upper j
  let Lw : Fin A.tapeCount → ℤ := dA.lower
  let Uw : Fin A.tapeCount → ℤ := fun j =>
    if j = outA then max (dA.upper outA) (dA.position outA + output.length) else dA.upper j
  have hUw_le : ∀ j, Uw j ≤ (S_int : ℤ) + 1 := by
    intro j
    dsimp [Uw]
    by_cases hj : j = outA
    · subst j
      rw [if_pos rfl]
      by_cases ho : output.length = 0
      · have := hwA outA; have := (hdA_bounds outA).2; omega
      · have hk := hsup6_out (output.length - 1) (by omega)
        have := (hdA_bounds outA).2; omega
    · rw [if_neg hj]; have := (hdA_bounds j).2; omega
  have hLw_ge : ∀ j, -(S_int : ℤ) ≤ Lw j := fun j => (hdA_bounds j).1
  -- Phase 9: wipeAll
  obtain ⟨t9, p9, l9, u9, n9, htr9, hn9, ht9_io, hp9_io, hclean9, hw9, henv9⟩ :=
    rPhase_wipeAll A outA Lw Uw t8 p8 l8 u8 L_env U_env hw8 henv8
      (fun j => ⟨by dsimp [L_env, B]; have := hLw_ge j; omega,
                 by dsimp [U_env, B]; have := hUw_le j; omega,
                 by dsimp [L_env, B]; have := hLw_ge j; omega,
                 by dsimp [U_env, B]; have := hUw_le j; omega⟩)
      (fun j => by
        rw [(hout8 _ (by simp)).2.1, (hout8 _ (by simp)).2.1]
        by_cases hj : j = outA
        · subst j; rw [hp7_M, hp7_D]
        · have h1 := hout7 (tMark j) (by simp) (by simp) (by simp [hj])
          have h2 := hout7 (tData j) (by simp) (by simp [hj]) (by simp)
          rw [h1.2.1, h2.2.1, (hM6 j).1, (hD6 j).2])
      (fun j => by
        rw [(hout8 _ (by simp)).2.1, (hout8 _ (by simp)).1]
        by_cases hj : j = outA
        · subst j; simp only [Lw, Uw, ↓reduceIte, hp7_M]; exact hmM7_out
        · have h1 := hout7 (tMark j) (by simp) (by simp) (by simp [hj])
          simp only [Lw, Uw, hj, ↓reduceIte, h1.1, h1.2.1]
          exact (hM6 j).2)
      (fun j => by
        rw [(hout8 _ (by simp)).2.1, (hout8 _ (by simp)).1]
        by_cases hj : j = outA
        · subst j; simp only [Lw, Uw, ↓reduceIte, hp7_D]; exact hD7_out
        · have h1 := hout7 (tData j) (by simp) (by simp [hj]) (by simp)
          simp only [Lw, Uw, hj, ↓reduceIte, h1.1, h1.2.1]
          intro z hz
          apply hsupA j z
          simpa [(hD6 j).1, (hD6 j).2] using hz)
  have htr_full : Computation.Trace (locatedStep R)
      (n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + n9))))))))
      (locatedInit R input)
      (cCfg (rOps A outA) (rStart A) tIO (.inl true) t9 p9 l9 u9) := by
    rw [hinit_eq]
    exact Trace.append htr1 (Trace.append htr2 (Trace.append htr3 (Trace.append htr4
      (Trace.append htr5 (Trace.append htr6 (Trace.append htr7 (Trace.append htr8 htr9)))))))
  let n_tot := n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + n9)))))))
  have hn_bound : (n_tot : ℝ) ≤ (C : ℝ) * (τ + σ + 1) := by
    have hsum_wipe : ∑ j : Fin A.tapeCount, (11 * (Uw j - Lw j + 2).toNat + 10) ≤
        A.tapeCount * (22 * S_int + 43) := by
      calc ∑ j : Fin A.tapeCount, (11 * (Uw j - Lw j + 2).toNat + 10)
          ≤ ∑ _j : Fin A.tapeCount, (22 * S_int + 43) := by
            apply Finset.sum_le_sum
            intro j _
            have := hLw_ge j; have := hUw_le j; omega
        _ = A.tapeCount * (22 * S_int + 43) := by simp
    have h12 : n1 + n2 + n3 + n4 + n5 ≤ A.tapeCount + 14 * input.length + 10 := by omega
    have h78 : n7 + n8 ≤ 9 * output.length + 4 := by
      have hlen7 := hn7
      have hdiff : (p7 (tMark outA) - dA.position outA).toNat = output.length := by rw [hp7_M]; omega
      omega
    have hn_nat : n_tot ≤ 4 * steps + (A.tapeCount * (22 * S_int + 43) + A.tapeCount +
        14 * input.length + 9 * output.length + 25) := by
      dsimp [n_tot]; omega
    have hS_step : (steps : ℝ) ≤ τ := hsteps_le
    have hS_in : (input.length : ℝ) ≤ σ := hin_len
    have hS_out : (output.length : ℝ) ≤ σ := hout_len
    have hmulS : (A.tapeCount : ℝ) * (S_int : ℝ) ≤ (A.tapeCount : ℝ) * σ :=
      mul_le_mul_of_nonneg_left hS_real (Nat.cast_nonneg _)
    have hn_real : (n_tot : ℝ) ≤ 4 * τ + (22 * (A.tapeCount : ℝ) + 23) * σ + (44 * (A.tapeCount : ℝ) + 25) := by
      have hn_r : (n_tot : ℝ) ≤ 4 * (steps : ℝ) +
          ((A.tapeCount : ℝ) * (22 * (S_int : ℝ) + 43) + (A.tapeCount : ℝ) +
            14 * (input.length : ℝ) + 9 * (output.length : ℝ) + 25) := by
        exact_mod_cast hn_nat
      linarith only [hn_r, hmulS, hS_step, hS_in, hS_out]
    have hC_ge1 : (4 : ℝ) ≤ (C : ℝ) := by dsimp [C]; exact_mod_cast (by omega : 4 ≤ 45 * A.tapeCount + 45)
    have hC_ge2 : (22 * (A.tapeCount : ℝ) + 23 : ℝ) ≤ (C : ℝ) := by
      dsimp [C]; exact_mod_cast (by omega : 22 * A.tapeCount + 23 ≤ 45 * A.tapeCount + 45)
    have hC_ge3 : (44 * (A.tapeCount : ℝ) + 25 : ℝ) ≤ (C : ℝ) := by
      dsimp [C]; exact_mod_cast (by omega : 44 * A.tapeCount + 25 ≤ 45 * A.tapeCount + 45)
    have hmul1 : 4 * τ ≤ (C : ℝ) * τ := mul_le_mul_of_nonneg_right hC_ge1 hτ
    have hmul2 : (22 * (A.tapeCount : ℝ) + 23) * σ ≤ (C : ℝ) * σ :=
      mul_le_mul_of_nonneg_right hC_ge2 hσ
    calc (n_tot : ℝ)
        ≤ 4 * τ + (22 * (A.tapeCount : ℝ) + 23) * σ + (44 * (A.tapeCount : ℝ) + 25) := hn_real
      _ ≤ (C : ℝ) * τ + (C : ℝ) * σ + (C : ℝ) := by linarith only [hmul1, hmul2, hC_ge3]
      _ = (C : ℝ) * (τ + σ + 1) := by ring
  refine ⟨n_tot, B, cCfg (rOps A outA) (rStart A) tIO (.inl true) t9 p9 l9 u9, htr_full,
    ⟨true, rfl⟩, ?_, ?_, ?_, hn_bound, ?_, ?_⟩
  · simp only [cCfg, R, resetMachine, cMachine, packTapes_apply]
    rw [ht9_io]; exact ht8_io_eq
  · intro j hj
    obtain ⟨r, rfl⟩ := (Fintype.equivFin (RTape A.tapeCount)).surjective j
    have hr_ne : r ≠ tIO := fun h => hj (by simp [h, R, resetMachine, cMachine])
    simp only [cCfg, packTapes_apply]
    rcases r with _ | i | i
    · exact (hr_ne rfl).elim
    · exact (hclean9 i).1
    · exact (hclean9 i).2.1
  · intro j
    obtain ⟨r, rfl⟩ := (Fintype.equivFin (RTape A.tapeCount)).surjective j
    simp only [cCfg, packTapes_apply]
    rcases r with _ | i | i
    · rw [hp9_io, hp8_io]
    · exact (hclean9 i).2.2.1
    · exact (hclean9 i).2.2.2
  · have hB_real : (B : ℝ) ≤ 3 * σ + 4 := by
      have hB_r : (B : ℝ) ≤ (S_int : ℝ) + max (input.length : ℝ) (output.length : ℝ) + 4 := by
        dsimp [B]; exact_mod_cast (by omega : S_int + max input.length output.length + 4 ≤
          S_int + max input.length output.length + 4)
      have hmax : max (input.length : ℝ) (output.length : ℝ) ≤ σ := max_le hin_len hout_len
      linarith only [hB_r, hS_real, hmax]
    have hC_B1 : (3 : ℝ) ≤ (C : ℝ) := by dsimp [C]; exact_mod_cast (by omega : 3 ≤ 45 * A.tapeCount + 45)
    have hC_B2 : (4 : ℝ) ≤ (C : ℝ) := by dsimp [C]; exact_mod_cast (by omega : 4 ≤ 45 * A.tapeCount + 45)
    have hmulB : 3 * σ ≤ (C : ℝ) * σ := mul_le_mul_of_nonneg_right hC_B1 hσ
    calc (B : ℝ) ≤ 3 * σ + 4 := hB_real
      _ ≤ (C : ℝ) * σ + (C : ℝ) := by linarith only [hmulB, hC_B2]
      _ = (C : ℝ) * (σ + 1) := by ring
  · intro j
    obtain ⟨r, rfl⟩ := (Fintype.equivFin (RTape A.tapeCount)).surjective j
    simp only [cCfg, packTapes_apply]
    exact henv9 r
