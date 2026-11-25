-- Prove2me | solution 1 for DetDLP.m89_polyT_oracle_loop
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T02:50:33.781296+00:00
-- url     : https://prove2.me/submissions/02bca049-8755-4ac3-b92a-a80fcd586dfc

import Mathlib
import Definitions.Def_DetDLP_Machine
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_DetDLP_PolyTBridge
import Definitions.Def_DetDLP_M89_CompileSpace
import Definitions.Def_DetDLP_M89_MachineComp
import Theorems.Thm_DetDLP_m89_resettable_machine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace DetDLP.M89OracleLoop

open DetDLP DetDLP.MachineComposition
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-! ## Section 1: Extensional `absCell` Tape Algebra & Trace Bounds -/

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
  · have hne : z - p ≠ 0 := sub_ne_zero.mpr h
    simp [h, hne]

theorem absCell_write_self (t : Turing.Tape (Option Bool)) (p : ℤ) :
    absCell (t.write t.head) p = absCell t p := by
  rw [Turing.Tape.write_self]

theorem tape_ext {t₁ t₂ : Turing.Tape (Option Bool)}
    (h : ∀ z : ℤ, t₁.nth z = t₂.nth z) : t₁ = t₂ := by
  rcases t₁ with ⟨h₁, L₁, R₁⟩
  rcases t₂ with ⟨h₂, L₂, R₂⟩
  have hh : h₁ = h₂ := h 0
  have hL : L₁ = L₂ := Turing.ListBlank.ext fun n => h (-(n + 1 : ℕ))
  have hR : R₁ = R₂ := Turing.ListBlank.ext fun n => h (n + 1 : ℕ)
  subst hh; subst hL; subst hR; rfl

theorem tape_ext_absCell {t₁ t₂ : Turing.Tape (Option Bool)} (p : ℤ)
    (h : ∀ z : ℤ, absCell t₁ p z = absCell t₂ p z) : t₁ = t₂ := by
  apply tape_ext
  intro k
  simpa [absCell] using h (p + k)

theorem nth_mk₁_nil (k : ℤ) :
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
    apply tape_ext_absCell p
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

theorem loc_ext {M : PrimitiveMachine} {c d : LocatedCfg M}
    (hs : c.config.state = d.config.state)
    (ht : ∀ j : Fin M.tapeCount, c.config.tapes j = d.config.tapes j)
    (hp : ∀ j : Fin M.tapeCount, c.position j = d.position j)
    (hl : ∀ j : Fin M.tapeCount, c.lower j = d.lower j)
    (hu : ∀ j : Fin M.tapeCount, c.upper j = d.upper j) : c = d := by
  rcases c with ⟨⟨sc, tc⟩, pc, lc, uc⟩
  rcases d with ⟨⟨sd, td⟩, pd, ld, ud⟩
  dsimp at hs
  subst hs
  have ht' : tc = td := funext ht
  have hp' : pc = pd := funext hp
  have hl' : lc = ld := funext hl
  have hu' : uc = ud := funext hu
  subst ht'; subst hp'; subst hl'; subst hu'; rfl

theorem locatedStep_bounds_mono {M : PrimitiveMachine} {a b : LocatedCfg M}
    (h : locatedStep M a = some b) (j : Fin M.tapeCount) :
    b.lower j ≤ a.lower j ∧ a.upper j ≤ b.upper j := by
  unfold locatedStep at h
  cases hstep : M.step a.config with
  | none => simp [hstep] at h
  | some cfg' =>
    have hb : a.monitor cfg' = b := by simpa [hstep] using h
    subst b
    rcases a with ⟨⟨st, tapes⟩, pos, low, upp⟩
    cases st with
    | inl b => simp [PrimitiveMachine.step] at hstep
    | inr q =>
      simp only [PrimitiveMachine.step] at hstep
      cases htr : M.transition q (tapes (M.scan q)).head with
      | inl ans =>
        simp only [htr, Option.some.injEq] at hstep; subst hstep
        simp [LocatedCfg.monitor, htr]
      | inr qa =>
        rcases qa with ⟨q', act⟩
        simp only [htr, Option.some.injEq] at hstep; subst hstep
        by_cases hj : j = M.scan q
        · subst j; simp [LocatedCfg.monitor, htr]
        · simp [LocatedCfg.monitor, htr, hj]

theorem locatedTrace_bounds_mono {M : PrimitiveMachine} {n : ℕ} {a b : LocatedCfg M}
    (ht : Computation.Trace (locatedStep M) n a b) (j : Fin M.tapeCount) :
    b.lower j ≤ a.lower j ∧ a.upper j ≤ b.upper j := by
  induction ht with
  | refl => exact ⟨le_rfl, le_rfl⟩
  | cons hstep _ ih =>
    have h1 := locatedStep_bounds_mono hstep j
    exact ⟨le_trans ih.1 h1.1, le_trans h1.2 ih.2⟩

theorem trace_prepend1 {α : Type*} {f : α → Option α} {n : ℕ} {a b d : α}
    (h1 : f a = some b) (ht : Computation.Trace f n b d) :
    Computation.Trace f (1 + n) a d := by
  simpa [Nat.add_comm] using .cons h1 ht

theorem trace_prepend2 {α : Type*} {f : α → Option α} {n : ℕ} {a b c d : α}
    (h1 : f a = some b) (h2 : f b = some c) (ht : Computation.Trace f n c d) :
    Computation.Trace f (2 + n) a d := by
  simpa [Nat.add_comm] using .cons h1 (.cons h2 ht)

theorem trace_prepend3 {α : Type*} {f : α → Option α} {n : ℕ} {a b c e d : α}
    (h1 : f a = some b) (h2 : f b = some c) (h3 : f c = some e)
    (ht : Computation.Trace f n e d) : Computation.Trace f (3 + n) a d := by
  simpa [Nat.add_comm] using .cons h1 (.cons h2 (.cons h3 ht))

theorem trace_prepend4 {α : Type*} {f : α → Option α} {n : ℕ} {a b c e g d : α}
    (h1 : f a = some b) (h2 : f b = some c) (h3 : f c = some e) (h4 : f e = some g)
    (ht : Computation.Trace f n g d) : Computation.Trace f (4 + n) a d := by
  simpa [Nat.add_comm] using .cons h1 (.cons h2 (.cons h3 (.cons h4 ht)))

theorem trace_prepend6 {α : Type*} {f : α → Option α} {n : ℕ} {a b c e g h d' d : α}
    (h1 : f a = some b) (h2 : f b = some c) (h3 : f c = some e) (h4 : f e = some g)
    (h5 : f g = some h) (h6 : f h = some d') (ht : Computation.Trace f n d' d) :
    Computation.Trace f (6 + n) a d := by
  simpa [Nat.add_comm] using .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 ht)))))

theorem polyBound_mono (K a b : ℕ) (h : a ≤ b) : polyBound K a ≤ polyBound K b := by
  simp only [polyBound]
  gcongr

private theorem polyBound_nonneg (K u : ℕ) : 0 ≤ polyBound K u := by
  unfold polyBound; positivity

end TapeHelpers

/-! ## Section 2: `COpMachine` Combinator -/

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

/-! ## Section 3: Compact Multi-Round Oracle Loop Machine `loopMachine` -/

section LoopBlock

abbrev LTape (r1 r2 : ℕ) := Fin 2 ⊕ Fin r1 ⊕ Fin r2
abbrev LQ (s1 s2 : ℕ) := Fin 78 ⊕ Fin s1 ⊕ Fin s2

abbrev tSt {r1 r2 : ℕ} : LTape r1 r2 := .inl 0
abbrev tAns {r1 r2 : ℕ} : LTape r1 r2 := .inl 1
abbrev tR1 {r1 r2 : ℕ} (j : Fin r1) : LTape r1 r2 := .inr (.inl j)
abbrev tR2 {r1 r2 : ℕ} (j : Fin r2) : LTape r1 r2 := .inr (.inr j)

@[simp] theorem ltape_st_ne_ans {r1 r2 : ℕ} : (tSt : LTape r1 r2) ≠ tAns := by simp
@[simp] theorem ltape_st_ne_r1 {r1 r2 : ℕ} (j : Fin r1) : (tSt : LTape r1 r2) ≠ tR1 j := by simp
@[simp] theorem ltape_st_ne_r2 {r1 r2 : ℕ} (j : Fin r2) : (tSt : LTape r1 r2) ≠ tR2 j := by simp
@[simp] theorem ltape_ans_ne_r1 {r1 r2 : ℕ} (j : Fin r1) : (tAns : LTape r1 r2) ≠ tR1 j := by simp
@[simp] theorem ltape_ans_ne_r2 {r1 r2 : ℕ} (j : Fin r2) : (tAns : LTape r1 r2) ≠ tR2 j := by simp
@[simp] theorem ltape_r1_ne_r2 {r1 r2 : ℕ} (j : Fin r1) (k : Fin r2) :
    (tR1 j : LTape r1 r2) ≠ tR2 k := by simp

private abbrev lq {s1 s2 : ℕ} (i : ℕ) (h : i < 78 := by omega) : LQ s1 s2 := .inl ⟨i, h⟩

abbrev qEncStCheck {s1 s2 : ℕ} : LQ s1 s2 := lq 0
abbrev qEncStW1T {s1 s2 : ℕ} : LQ s1 s2 := lq 1
abbrev qEncStAdv1T {s1 s2 : ℕ} : LQ s1 s2 := lq 2
abbrev qEncStW2T {s1 s2 : ℕ} : LQ s1 s2 := lq 3
abbrev qEncStW1F {s1 s2 : ℕ} : LQ s1 s2 := lq 4
abbrev qEncStAdv1F {s1 s2 : ℕ} : LQ s1 s2 := lq 5
abbrev qEncStW2F {s1 s2 : ℕ} : LQ s1 s2 := lq 6
abbrev qEncStAdv2 {s1 s2 : ℕ} : LQ s1 s2 := lq 7
abbrev qEncStAdvSrc {s1 s2 : ℕ} : LQ s1 s2 := lq 8
abbrev qEncSep {s1 s2 : ℕ} : LQ s1 s2 := lq 9
abbrev qEncSepAdv {s1 s2 : ℕ} : LQ s1 s2 := lq 10

abbrev qEncAnsCheck {s1 s2 : ℕ} : LQ s1 s2 := lq 11
abbrev qEncAnsWT {s1 s2 : ℕ} : LQ s1 s2 := lq 12
abbrev qEncAnsWF {s1 s2 : ℕ} : LQ s1 s2 := lq 13
abbrev qEncAnsAdvD {s1 s2 : ℕ} : LQ s1 s2 := lq 14
abbrev qEncAnsAdvS {s1 s2 : ℕ} : LQ s1 s2 := lq 15

abbrev qEraseStStart {s1 s2 : ℕ} : LQ s1 s2 := lq 16
abbrev qEraseStCheck {s1 s2 : ℕ} : LQ s1 s2 := lq 17
abbrev qEraseStW {s1 s2 : ℕ} : LQ s1 s2 := lq 18
abbrev qEraseStRight {s1 s2 : ℕ} : LQ s1 s2 := lq 19

abbrev qEraseAnsStart {s1 s2 : ℕ} : LQ s1 s2 := lq 20
abbrev qEraseAnsCheck {s1 s2 : ℕ} : LQ s1 s2 := lq 21
abbrev qEraseAnsW {s1 s2 : ℕ} : LQ s1 s2 := lq 22
abbrev qEraseAnsRight {s1 s2 : ℕ} : LQ s1 s2 := lq 23

abbrev qRewR1Start {s1 s2 : ℕ} : LQ s1 s2 := lq 24
abbrev qRewR1Check {s1 s2 : ℕ} : LQ s1 s2 := lq 25
abbrev qRewR1Right {s1 s2 : ℕ} : LQ s1 s2 := lq 26

abbrev qBranchOut {s1 s2 : ℕ} : LQ s1 s2 := lq 27
abbrev qDoneAdv {s1 s2 : ℕ} : LQ s1 s2 := lq 28
abbrev qDoneCopyCheck {s1 s2 : ℕ} : LQ s1 s2 := lq 29
abbrev qDoneCopyWT {s1 s2 : ℕ} : LQ s1 s2 := lq 30
abbrev qDoneCopyWF {s1 s2 : ℕ} : LQ s1 s2 := lq 31
abbrev qDoneCopyAdvD {s1 s2 : ℕ} : LQ s1 s2 := lq 32
abbrev qDoneCopyAdvS {s1 s2 : ℕ} : LQ s1 s2 := lq 33
abbrev qRewStDoneStart {s1 s2 : ℕ} : LQ s1 s2 := lq 34
abbrev qRewStDoneCheck {s1 s2 : ℕ} : LQ s1 s2 := lq 35
abbrev qRewStDoneRight {s1 s2 : ℕ} : LQ s1 s2 := lq 36
abbrev qEraseR1DoneStart {s1 s2 : ℕ} : LQ s1 s2 := lq 37
abbrev qEraseR1DoneCheck {s1 s2 : ℕ} : LQ s1 s2 := lq 38
abbrev qEraseR1DoneW {s1 s2 : ℕ} : LQ s1 s2 := lq 39
abbrev qEraseR1DoneRight {s1 s2 : ℕ} : LQ s1 s2 := lq 40
abbrev qHalt {s1 s2 : ℕ} : LQ s1 s2 := lq 41

abbrev qDecAdv {s1 s2 : ℕ} : LQ s1 s2 := lq 42
abbrev qDecCheck1 {s1 s2 : ℕ} : LQ s1 s2 := lq 43
abbrev qDecAdv1 {s1 s2 : ℕ} : LQ s1 s2 := lq 44
abbrev qDecBit {s1 s2 : ℕ} : LQ s1 s2 := lq 45
abbrev qDecStWT {s1 s2 : ℕ} : LQ s1 s2 := lq 46
abbrev qDecStWF {s1 s2 : ℕ} : LQ s1 s2 := lq 47
abbrev qDecAdvSt {s1 s2 : ℕ} : LQ s1 s2 := lq 48
abbrev qDecAdv2 {s1 s2 : ℕ} : LQ s1 s2 := lq 49
abbrev qDecSepAdv {s1 s2 : ℕ} : LQ s1 s2 := lq 50

abbrev qDecQCheck {s1 s2 : ℕ} : LQ s1 s2 := lq 51
abbrev qDecQWT {s1 s2 : ℕ} : LQ s1 s2 := lq 52
abbrev qDecQWF {s1 s2 : ℕ} : LQ s1 s2 := lq 53
abbrev qDecQAdvD {s1 s2 : ℕ} : LQ s1 s2 := lq 54
abbrev qDecQAdvS {s1 s2 : ℕ} : LQ s1 s2 := lq 55

abbrev qRewStDecStart {s1 s2 : ℕ} : LQ s1 s2 := lq 56
abbrev qRewStDecCheck {s1 s2 : ℕ} : LQ s1 s2 := lq 57
abbrev qRewStDecRight {s1 s2 : ℕ} : LQ s1 s2 := lq 58

abbrev qRewR2DecStart {s1 s2 : ℕ} : LQ s1 s2 := lq 59
abbrev qRewR2DecCheck {s1 s2 : ℕ} : LQ s1 s2 := lq 60
abbrev qRewR2DecRight {s1 s2 : ℕ} : LQ s1 s2 := lq 61

abbrev qEraseR1DecStart {s1 s2 : ℕ} : LQ s1 s2 := lq 62
abbrev qEraseR1DecCheck {s1 s2 : ℕ} : LQ s1 s2 := lq 63
abbrev qEraseR1DecW {s1 s2 : ℕ} : LQ s1 s2 := lq 64
abbrev qEraseR1DecRight {s1 s2 : ℕ} : LQ s1 s2 := lq 65

abbrev qRetAnsCheck {s1 s2 : ℕ} : LQ s1 s2 := lq 66
abbrev qRetAnsWT {s1 s2 : ℕ} : LQ s1 s2 := lq 67
abbrev qRetAnsWF {s1 s2 : ℕ} : LQ s1 s2 := lq 68
abbrev qRetAnsAdvD {s1 s2 : ℕ} : LQ s1 s2 := lq 69
abbrev qRetAnsAdvS {s1 s2 : ℕ} : LQ s1 s2 := lq 70

abbrev qRewAnsRetStart {s1 s2 : ℕ} : LQ s1 s2 := lq 71
abbrev qRewAnsRetCheck {s1 s2 : ℕ} : LQ s1 s2 := lq 72
abbrev qRewAnsRetRight {s1 s2 : ℕ} : LQ s1 s2 := lq 73

abbrev qEraseR2RetStart {s1 s2 : ℕ} : LQ s1 s2 := lq 74
abbrev qEraseR2RetCheck {s1 s2 : ℕ} : LQ s1 s2 := lq 75
abbrev qEraseR2RetW {s1 s2 : ℕ} : LQ s1 s2 := lq 76
abbrev qEraseR2RetRight {s1 s2 : ℕ} : LQ s1 s2 := lq 77

def loopOps (R₁ R₂ : PrimitiveMachine) :
    LQ R₁.stateCount R₂.stateCount → COp (LQ R₁.stateCount R₂.stateCount) (LTape R₁.tapeCount R₂.tapeCount)
  | .inl idx =>
    let in1 := tR1 R₁.inputTape
    let in2 := tR2 R₂.inputTape
    match idx.val with
    | 0 => .branch tSt fun | none => qEncSep | some true => qEncStW1T | some false => qEncStW1F
    | 1 => .act in1 (.write (some true)) qEncStAdv1T
    | 2 => .act in1 (.move .right) qEncStW2T
    | 3 => .act in1 (.write (some true)) qEncStAdv2
    | 4 => .act in1 (.write (some true)) qEncStAdv1F
    | 5 => .act in1 (.move .right) qEncStW2F
    | 6 => .act in1 (.write (some false)) qEncStAdv2
    | 7 => .act in1 (.move .right) qEncStAdvSrc
    | 8 => .act tSt (.move .right) qEncStCheck
    | 9 => .act in1 (.write (some false)) qEncSepAdv
    | 10 => .act in1 (.move .right) qEncAnsCheck
    | 11 => .branch tAns fun | none => qEraseStStart | some true => qEncAnsWT | some false => qEncAnsWF
    | 12 => .act in1 (.write (some true)) qEncAnsAdvD
    | 13 => .act in1 (.write (some false)) qEncAnsAdvD
    | 14 => .act in1 (.move .right) qEncAnsAdvS
    | 15 => .act tAns (.move .right) qEncAnsCheck
    | 16 => .act tSt (.move .left) qEraseStCheck
    | 17 => .branch tSt fun | none => qEraseStRight | some _ => qEraseStW
    | 18 => .act tSt (.write none) qEraseStStart
    | 19 => .act tSt (.move .right) qEraseAnsStart
    | 20 => .act tAns (.move .left) qEraseAnsCheck
    | 21 => .branch tAns fun | none => qEraseAnsRight | some _ => qEraseAnsW
    | 22 => .act tAns (.write none) qEraseAnsStart
    | 23 => .act tAns (.move .right) qRewR1Start
    | 24 => .act in1 (.move .left) qRewR1Check
    | 25 => .branch in1 fun | none => qRewR1Right | some _ => qRewR1Start
    | 26 => .act in1 (.move .right) (.inr (.inl R₁.start))
    | 27 => .branch in1 fun | some true => qDoneAdv | some false => qDecAdv | none => qDoneAdv
    | 28 => .act in1 (.move .right) qDoneCopyCheck
    | 29 => .branch in1 fun | none => qRewStDoneStart | some true => qDoneCopyWT | some false => qDoneCopyWF
    | 30 => .act tSt (.write (some true)) qDoneCopyAdvD
    | 31 => .act tSt (.write (some false)) qDoneCopyAdvD
    | 32 => .act tSt (.move .right) qDoneCopyAdvS
    | 33 => .act in1 (.move .right) qDoneCopyCheck
    | 34 => .act tSt (.move .left) qRewStDoneCheck
    | 35 => .branch tSt fun | none => qRewStDoneRight | some _ => qRewStDoneStart
    | 36 => .act tSt (.move .right) qEraseR1DoneStart
    | 37 => .act in1 (.move .left) qEraseR1DoneCheck
    | 38 => .branch in1 fun | none => qEraseR1DoneRight | some _ => qEraseR1DoneW
    | 39 => .act in1 (.write none) qEraseR1DoneStart
    | 40 => .act in1 (.move .right) qHalt
    | 41 => .halt true
    | 42 => .act in1 (.move .right) qDecCheck1
    | 43 => .branch in1 fun | some true => qDecAdv1 | some false => qDecSepAdv | none => qDecSepAdv
    | 44 => .act in1 (.move .right) qDecBit
    | 45 => .branch in1 fun | some true => qDecStWT | some false => qDecStWF | none => qDecStWT
    | 46 => .act tSt (.write (some true)) qDecAdvSt
    | 47 => .act tSt (.write (some false)) qDecAdvSt
    | 48 => .act tSt (.move .right) qDecAdv2
    | 49 => .act in1 (.move .right) qDecCheck1
    | 50 => .act in1 (.move .right) qDecQCheck
    | 51 => .branch in1 fun | none => qRewStDecStart | some true => qDecQWT | some false => qDecQWF
    | 52 => .act in2 (.write (some true)) qDecQAdvD
    | 53 => .act in2 (.write (some false)) qDecQAdvD
    | 54 => .act in2 (.move .right) qDecQAdvS
    | 55 => .act in1 (.move .right) qDecQCheck
    | 56 => .act tSt (.move .left) qRewStDecCheck
    | 57 => .branch tSt fun | none => qRewStDecRight | some _ => qRewStDecStart
    | 58 => .act tSt (.move .right) qRewR2DecStart
    | 59 => .act in2 (.move .left) qRewR2DecCheck
    | 60 => .branch in2 fun | none => qRewR2DecRight | some _ => qRewR2DecStart
    | 61 => .act in2 (.move .right) qEraseR1DecStart
    | 62 => .act in1 (.move .left) qEraseR1DecCheck
    | 63 => .branch in1 fun | none => qEraseR1DecRight | some _ => qEraseR1DecW
    | 64 => .act in1 (.write none) qEraseR1DecStart
    | 65 => .act in1 (.move .right) (.inr (.inr R₂.start))
    | 66 => .branch in2 fun | none => qRewAnsRetStart | some true => qRetAnsWT | some false => qRetAnsWF
    | 67 => .act tAns (.write (some true)) qRetAnsAdvD
    | 68 => .act tAns (.write (some false)) qRetAnsAdvD
    | 69 => .act tAns (.move .right) qRetAnsAdvS
    | 70 => .act in2 (.move .right) qRetAnsCheck
    | 71 => .act tAns (.move .left) qRewAnsRetCheck
    | 72 => .branch tAns fun | none => qRewAnsRetRight | some _ => qRewAnsRetStart
    | 73 => .act tAns (.move .right) qEraseR2RetStart
    | 74 => .act in2 (.move .left) qEraseR2RetCheck
    | 75 => .branch in2 fun | none => qEraseR2RetRight | some _ => qEraseR2RetW
    | 76 => .act in2 (.write none) qEraseR2RetStart
    | _ => .act in2 (.move .right) qEncStCheck
  | .inr (.inl q1) =>
    .raw (tR1 (R₁.scan q1)) fun sym =>
      match R₁.transition q1 sym with
      | .inl _ => .inr (qBranchOut, .write sym)
      | .inr (q1', stmt) => .inr (.inr (.inl q1'), stmt)
  | .inr (.inr q2) =>
    .raw (tR2 (R₂.scan q2)) fun sym =>
      match R₂.transition q2 sym with
      | .inl _ => .inr (qRetAnsCheck, .write sym)
      | .inr (q2', stmt) => .inr (.inr (.inr q2'), stmt)

noncomputable abbrev loopMachine (R₁ R₂ : PrimitiveMachine) : PrimitiveMachine :=
  cMachine (loopOps R₁ R₂) qEncStCheck tSt

abbrev LCfg (r1 r2 : ℕ) := LTape r1 r2 → Turing.Tape (Option Bool)
abbrev LPos (r1 r2 : ℕ) := LTape r1 r2 → ℤ

section Steps
variable (R₁ R₂ : PrimitiveMachine)

private theorem lStep_halt {q : LQ R₁.stateCount R₂.stateCount} {b : Bool}
    (h : loopOps R₁ R₂ q = .halt b) (t : LCfg R₁.tapeCount R₂.tapeCount)
    (p l u : LPos R₁.tapeCount R₂.tapeCount) :
    locatedStep (loopMachine R₁ R₂) (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr q) t p l u) =
      some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inl b) t p l u) :=
  cStep_halt h t p l u

private theorem lStep_write {q q' : LQ R₁.stateCount R₂.stateCount}
    {k : LTape R₁.tapeCount R₂.tapeCount} {sym : Option Bool}
    (h : loopOps R₁ R₂ q = .act k (.write sym) q') (t : LCfg R₁.tapeCount R₂.tapeCount)
    (p l u : LPos R₁.tapeCount R₂.tapeCount) (hw : l k ≤ p k ∧ p k ≤ u k) :
    locatedStep (loopMachine R₁ R₂) (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr q) t p l u) =
      some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr q')
        (Function.update t k ((t k).write sym)) p l u) :=
  cStep_write h t p l u hw

private theorem lStep_move_right {q q' : LQ R₁.stateCount R₂.stateCount}
    {k : LTape R₁.tapeCount R₂.tapeCount}
    (h : loopOps R₁ R₂ q = .act k (.move .right) q') (t : LCfg R₁.tapeCount R₂.tapeCount)
    (p l u : LPos R₁.tapeCount R₂.tapeCount) :
    locatedStep (loopMachine R₁ R₂) (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr q) t p l u) =
      some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr q')
        (Function.update t k ((t k).move .right))
        (Function.update p k (p k + 1))
        (Function.update l k (min (l k) (p k + 1)))
        (Function.update u k (max (u k) (p k + 1)))) := by
  simpa [headDisplacement] using cStep_move h t p l u

private theorem lStep_move_left {q q' : LQ R₁.stateCount R₂.stateCount}
    {k : LTape R₁.tapeCount R₂.tapeCount}
    (h : loopOps R₁ R₂ q = .act k (.move .left) q') (t : LCfg R₁.tapeCount R₂.tapeCount)
    (p l u : LPos R₁.tapeCount R₂.tapeCount) :
    locatedStep (loopMachine R₁ R₂) (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr q) t p l u) =
      some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr q')
        (Function.update t k ((t k).move .left))
        (Function.update p k (p k - 1))
        (Function.update l k (min (l k) (p k - 1)))
        (Function.update u k (max (u k) (p k - 1)))) := by
  simpa [headDisplacement, sub_eq_add_neg] using cStep_move h t p l u

private theorem lStep_branch {q : LQ R₁.stateCount R₂.stateCount}
    {k : LTape R₁.tapeCount R₂.tapeCount}
    {next : Option Bool → LQ R₁.stateCount R₂.stateCount}
    (h : loopOps R₁ R₂ q = .branch k next) (t : LCfg R₁.tapeCount R₂.tapeCount)
    (p l u : LPos R₁.tapeCount R₂.tapeCount) (hw : l k ≤ p k ∧ p k ≤ u k) :
    locatedStep (loopMachine R₁ R₂) (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr q) t p l u) =
      some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (next (t k).head)) t p l u) :=
  cStep_branch h t p l u hw

private theorem lStep_raw_move {q q' : LQ R₁.stateCount R₂.stateCount}
    {k : LTape R₁.tapeCount R₂.tapeCount}
    {tr : Option Bool → Bool ⊕ (LQ R₁.stateCount R₂.stateCount × Turing.TM0.Stmt (Option Bool))}
    {dir : Turing.Dir} (h : loopOps R₁ R₂ q = .raw k tr)
    (t : LCfg R₁.tapeCount R₂.tapeCount) (p l u : LPos R₁.tapeCount R₂.tapeCount)
    (htr : tr (t k).head = .inr (q', .move dir)) :
    let pos' := p k + headDisplacement (.move dir)
    locatedStep (loopMachine R₁ R₂) (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr q) t p l u) =
      some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr q')
        (Function.update t k ((t k).move dir))
        (Function.update p k pos')
        (Function.update l k (min (l k) pos'))
        (Function.update u k (max (u k) pos'))) :=
  cStep_raw_move h t p l u htr

private theorem lStep_raw_write {q q' : LQ R₁.stateCount R₂.stateCount}
    {k : LTape R₁.tapeCount R₂.tapeCount}
    {tr : Option Bool → Bool ⊕ (LQ R₁.stateCount R₂.stateCount × Turing.TM0.Stmt (Option Bool))}
    {sym : Option Bool} (h : loopOps R₁ R₂ q = .raw k tr)
    (t : LCfg R₁.tapeCount R₂.tapeCount) (p l u : LPos R₁.tapeCount R₂.tapeCount)
    (htr : tr (t k).head = .inr (q', .write sym)) (hw : l k ≤ p k ∧ p k ≤ u k) :
    locatedStep (loopMachine R₁ R₂) (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr q) t p l u) =
      some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr q')
        (Function.update t k ((t k).write sym)) p l u) :=
  cStep_raw_write h t p l u htr hw

end Steps

/-! ## Section 4: Generic Loop Phase Lemmas -/

section Phases
variable (R₁ R₂ : PrimitiveMachine)

private theorem lPhase_rewindLeft
    (qStart qCheck qRight qNext : LQ R₁.stateCount R₂.stateCount)
    (k : LTape R₁.tapeCount R₂.tapeCount) (len : ℕ)
    (h1 : loopOps R₁ R₂ qStart = .act k (.move .left) qCheck)
    (h2 : loopOps R₁ R₂ qCheck = .branch k fun | none => qRight | some _ => qStart)
    (h3 : loopOps R₁ R₂ qRight = .act k (.move .right) qNext)
    (t : LCfg R₁.tapeCount R₂.tapeCount) (p l u : LPos R₁.tapeCount R₂.tapeCount) (L_env U_env : ℤ)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r) (henv : ∀ r, L_env ≤ l r ∧ u r ≤ U_env)
    (hLk : L_env ≤ -1) (hUk : (len : ℤ) ≤ U_env) (hp : p k = len)
    (ht_neg1 : absCell (t k) (len : ℤ) (-1) = none)
    (ht_nonneg : ∀ z : ℤ, 0 ≤ z → z < (len : ℤ) → absCell (t k) (len : ℤ) z ≠ none) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qStart) t p l u)
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qNext) t1 p1 l1 u1) ∧
      n = 2 * len + 3 ∧
      (∀ r ≠ k, t1 r = t r ∧ p1 r = p r ∧ l1 r = l r ∧ u1 r = u r) ∧
      (∀ z : ℤ, absCell (t1 k) 0 z = absCell (t k) (len : ℤ) z) ∧
      p1 k = 0 ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) := by
  let tk0 := t k
  have loop2 : ∀ (m : ℕ) (_hm : m ≤ len) (t' : LCfg R₁.tapeCount R₂.tapeCount)
      (p' l' u' : LPos R₁.tapeCount R₂.tapeCount)
      (hw' : ∀ r, l' r ≤ p' r ∧ p' r ≤ u' r) (henv' : ∀ r, L_env ≤ l' r ∧ u' r ≤ U_env)
      (hp' : p' k = m)
      (ht_rel : ∀ z : ℤ, absCell (t' k) (m : ℤ) z = absCell tk0 (len : ℤ) z),
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qStart) t' p' l' u')
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qNext) t1 p1 l1 u1) ∧
        n = 2 * m + 3 ∧
        (∀ r ≠ k, t1 r = t' r ∧ p1 r = p' r ∧ l1 r = l' r ∧ u1 r = u' r) ∧
        (∀ z : ℤ, absCell (t1 k) 0 z = absCell tk0 (len : ℤ) z) ∧
        p1 k = 0 ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) := by
    intro m
    induction m with
    | zero =>
      intro _ t' p' l' u' hw' henv' hp' ht_rel
      have hs0 := lStep_move_left R₁ R₂ (q := qStart) (q' := qCheck) (k := k) h1 t' p' l' u'
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
      have hs1 := lStep_branch R₁ R₂ (q := qCheck) (k := k) h2 t_1 p_1 l_1 u' (hw1 k)
      rw [hhead] at hs1
      have hs2 := lStep_move_right R₁ R₂ (q := qRight) (q' := qNext) (k := k) h3 t_1 p_1 l_1 u'
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
      have henv2 : ∀ r, L_env ≤ l_2 r ∧ u_2 r ≤ U_env := by
        intro r; by_cases hr : r = k
        · subst r; have h1 := henv' k; have h2 := hw' k
          have hlo : l_2 k = min (min (l' k) (p' k - 1)) (p' k - 1 + 1) := by simp [l_2, l_1, p_1]
          have hhi : u_2 k = max (u' k) (p' k - 1 + 1) := by simp [u_2, p_1]
          rw [hlo, hhi, hp']
          exact ⟨le_min (le_min h1.1 (by omega)) (by omega), max_le h1.2 (by omega)⟩
        · simp only [l_2, l_1, u_2, Function.update_of_ne hr]; exact henv' r
      exact ⟨t_2, p_2, l_2, u_2, 3, .cons hs0 (.cons hs1 (.cons hs2 (.refl _))), rfl,
        fun r hr => by dsimp [t_2, t_1, p_2, p_1, l_2, l_1, u_2]; simp [hr],
        ht_eq, hp_eq, hw2, henv2⟩
    | succ m ih =>
      intro hm t' p' l' u' hw' henv' hp' ht_rel
      have hs0 := lStep_move_left R₁ R₂ (q := qStart) (q' := qCheck) (k := k) h1 t' p' l' u'
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
      have hs1 := lStep_branch R₁ R₂ (q := qCheck) (k := k) h2 t_1 p_1 l_1 u' (hw1 k)
      rw [hhead] at hs1
      have hp1 : p_1 k = m := by simp [p_1, hp']; try omega
      have hrel1 : ∀ z : ℤ, absCell (t_1 k) (m : ℤ) z = absCell tk0 (len : ℤ) z := by
        intro z
        have heq : t_1 k = (t' k).move .left := by simp [t_1]
        rw [heq, show (m : ℤ) = ((m + 1 : ℕ) : ℤ) - 1 by omega, absCell_move_left]
        exact ht_rel z
      have henv1 : ∀ r, L_env ≤ l_1 r ∧ u' r ≤ U_env := by
        intro r; by_cases hr : r = k
        · subst r; have h1 := henv' k; simp only [l_1, Function.update_self, hp']
          exact ⟨le_min h1.1 (by omega), h1.2⟩
        · simp only [l_1, Function.update_of_ne hr]; exact henv' r
      obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hout1, htz, hp1z, hw2, henv2⟩ :=
        ih (by omega) t_1 p_1 l_1 u' hw1 henv1 hp1 hrel1
      refine ⟨t1, p1, l1, u1, 2 + n1, trace_prepend2 hs0 hs1 htail,
        by omega, ?_, htz, hp1z, hw2, henv2⟩
      intro r hr
      have ho := hout1 r hr
      have hr' : t_1 r = t' r ∧ p_1 r = p' r ∧ l_1 r = l' r := by
        dsimp [t_1, p_1, l_1]; simp [hr]
      exact ⟨ho.1.trans hr'.1, ho.2.1.trans hr'.2.1, ho.2.2.1.trans hr'.2.2, ho.2.2.2⟩
  exact loop2 len le_rfl t p l u hw henv hp (fun _ => rfl)

private theorem lPhase_eraseLeft
    (qStart qCheck qWrite qRight qNext : LQ R₁.stateCount R₂.stateCount)
    (k : LTape R₁.tapeCount R₂.tapeCount) (len : ℕ)
    (h1 : loopOps R₁ R₂ qStart = .act k (.move .left) qCheck)
    (h2 : loopOps R₁ R₂ qCheck = .branch k fun | none => qRight | some _ => qWrite)
    (h3 : loopOps R₁ R₂ qWrite = .act k (.write none) qStart)
    (h4 : loopOps R₁ R₂ qRight = .act k (.move .right) qNext)
    (t : LCfg R₁.tapeCount R₂.tapeCount) (p l u : LPos R₁.tapeCount R₂.tapeCount) (L_env U_env : ℤ)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r) (henv : ∀ r, L_env ≤ l r ∧ u r ≤ U_env)
    (hL : L_env ≤ -1) (hU : (len : ℤ) ≤ U_env) (hp : p k = len)
    (ht : ∀ z : ℤ, absCell (t k) (len : ℤ) z = none ↔ ¬ (0 ≤ z ∧ z < (len : ℤ))) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qStart) t p l u)
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qNext) t1 p1 l1 u1) ∧
      n = 3 * len + 3 ∧
      (∀ r ≠ k, t1 r = t r ∧ p1 r = p r ∧ l1 r = l r ∧ u1 r = u r) ∧
      t1 k = Turing.Tape.mk₁ [] ∧ p1 k = 0 ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) := by
  have loop : ∀ (m : ℕ) (_hm : m ≤ len) (t' : LCfg R₁.tapeCount R₂.tapeCount)
      (p' l' u' : LPos R₁.tapeCount R₂.tapeCount)
      (hw' : ∀ r, l' r ≤ p' r ∧ p' r ≤ u' r) (henv' : ∀ r, L_env ≤ l' r ∧ u' r ≤ U_env)
      (hp' : p' k = m)
      (ht' : ∀ z : ℤ, absCell (t' k) (m : ℤ) z = none ↔ ¬ (0 ≤ z ∧ z < (m : ℤ))),
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qStart) t' p' l' u')
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qNext) t1 p1 l1 u1) ∧
        n = 3 * m + 3 ∧
        (∀ r ≠ k, t1 r = t' r ∧ p1 r = p' r ∧ l1 r = l' r ∧ u1 r = u' r) ∧
        t1 k = Turing.Tape.mk₁ [] ∧ p1 k = 0 ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) := by
    intro m
    induction m with
    | zero =>
      intro _ t' p' l' u' hw' henv' hp' ht'
      have hs0 := lStep_move_left R₁ R₂ (q := qStart) (q' := qCheck) (k := k) h1 t' p' l' u'
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
        have hs : (t_1 k).head = absCell ((t' k).move .left) (p' k - 1) (p' k - 1) := by
          simp [t_1, absCell_self]
        rw [hs, absCell_move_left, hp', ht']
        omega
      have hs1 := lStep_branch R₁ R₂ (q := qCheck) (k := k) h2 t_1 p_1 l_1 u' (hw1 k)
      rw [hhead] at hs1
      have hs2 := lStep_move_right R₁ R₂ (q := qRight) (q' := qNext) (k := k) h4 t_1 p_1 l_1 u'
      let t_2 := Function.update t_1 k ((t_1 k).move .right)
      let p_2 := Function.update p_1 k (p_1 k + 1)
      let l_2 := Function.update l_1 k (min (l_1 k) (p_1 k + 1))
      let u_2 := Function.update u' k (max (u' k) (p_1 k + 1))
      have ht_eq : t_2 k = Turing.Tape.mk₁ [] := by
        apply (blank_iff_absCell (p := (0 : ℤ))).1
        intro z
        have heq : t_2 k = t' k := by simp [t_2, t_1]
        rw [heq, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, ht']; omega
      have hp_eq : p_2 k = 0 := by simp [p_2, p_1, hp']
      have hw2 : ∀ r, l_2 r ≤ p_2 r ∧ p_2 r ≤ u_2 r := by
        intro r; by_cases hr : r = k
        · subst r; simp only [p_2, l_2, u_2, Function.update_self]
          exact ⟨min_le_right _ _, le_max_right _ _⟩
        · simp only [p_2, p_1, l_2, l_1, u_2, Function.update_of_ne hr]; exact hw' r
      have henv2 : ∀ r, L_env ≤ l_2 r ∧ u_2 r ≤ U_env := by
        intro r; by_cases hr : r = k
        · subst r; have h1 := henv' k
          have hlo : l_2 k = min (min (l' k) (p' k - 1)) (p' k - 1 + 1) := by simp [l_2, l_1, p_1]
          have hhi : u_2 k = max (u' k) (p' k - 1 + 1) := by simp [u_2, p_1]
          rw [hlo, hhi, hp']
          exact ⟨le_min (le_min h1.1 (by omega)) (by omega), max_le h1.2 (by omega)⟩
        · simp only [l_2, l_1, u_2, Function.update_of_ne hr]; exact henv' r
      exact ⟨t_2, p_2, l_2, u_2, 3, .cons hs0 (.cons hs1 (.cons hs2 (.refl _))), rfl,
        fun r hr => by dsimp [t_2, t_1, p_2, p_1, l_2, l_1, u_2]; simp [hr],
        ht_eq, hp_eq, hw2, henv2⟩
    | succ m ih =>
      intro hm t' p' l' u' hw' henv' hp' ht'
      have hs0 := lStep_move_left R₁ R₂ (q := qStart) (q' := qCheck) (k := k) h1 t' p' l' u'
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
        have hs : (t_1 k).head = absCell ((t' k).move .left) (p' k - 1) (p' k - 1) := by
          simp [t_1, absCell_self]
        intro hbad
        rw [hs, absCell_move_left, hp', ht'] at hbad
        omega
      rcases Option.ne_none_iff_exists'.1 hne with ⟨b, hhead⟩
      have hs1 := lStep_branch R₁ R₂ (q := qCheck) (k := k) h2 t_1 p_1 l_1 u' (hw1 k)
      rw [hhead] at hs1
      have hs2 := lStep_write R₁ R₂ (q := qWrite) (q' := qStart) (k := k) (sym := none) h3
        t_1 p_1 l_1 u' (hw1 k)
      let t_2 := Function.update t_1 k ((t_1 k).write none)
      have hp2 : p_1 k = m := by simp [p_1, hp']; try omega
      have ht2 : ∀ z : ℤ, absCell (t_2 k) (m : ℤ) z = none ↔ ¬ (0 ≤ z ∧ z < (m : ℤ)) := by
        intro z
        have heq : t_2 k = ((t' k).move .left).write none := by simp [t_2, t_1]
        rw [heq, show (m : ℤ) = ((m + 1 : ℕ) : ℤ) - 1 by omega, absCell_write, absCell_move_left]
        by_cases hz : z = ((m + 1 : ℕ) : ℤ) - 1
        · subst z; simp
        · rw [if_neg hz, ht' z]; omega
      have henv1 : ∀ r, L_env ≤ l_1 r ∧ u' r ≤ U_env := by
        intro r; by_cases hr : r = k
        · subst r; have h1 := henv' k; simp only [l_1, Function.update_self, hp']
          exact ⟨le_min h1.1 (by omega), h1.2⟩
        · simp only [l_1, Function.update_of_ne hr]; exact henv' r
      obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hout1, ht_eq, hp_eq, hw2, henv2⟩ :=
        ih (by omega) t_2 p_1 l_1 u' hw1 henv1 hp2 ht2
      refine ⟨t1, p1, l1, u1, 3 + n1, trace_prepend3 hs0 hs1 hs2 htail,
        by omega, ?_, ht_eq, hp_eq, hw2, henv2⟩
      intro r hr
      have ho := hout1 r hr
      have hr' : t_2 r = t' r ∧ p_1 r = p' r ∧ l_1 r = l' r := by
        dsimp [t_2, t_1, p_1, l_1]; simp [hr]
      exact ⟨ho.1.trans hr'.1, ho.2.1.trans hr'.2.1, ho.2.2.1.trans hr'.2.2, ho.2.2.2⟩
  exact loop len le_rfl t p l u hw henv hp ht

private theorem lPhase_copy
    (qCheck qWT qWF qAdvD qAdvS qNext : LQ R₁.stateCount R₂.stateCount)
    (src dst : LTape R₁.tapeCount R₂.tapeCount) (hne : src ≠ dst)
    (h1 : loopOps R₁ R₂ qCheck = .branch src fun | none => qNext | some true => qWT | some false => qWF)
    (h2 : loopOps R₁ R₂ qWT = .act dst (.write (some true)) qAdvD)
    (h3 : loopOps R₁ R₂ qWF = .act dst (.write (some false)) qAdvD)
    (h4 : loopOps R₁ R₂ qAdvD = .act dst (.move .right) qAdvS)
    (h5 : loopOps R₁ R₂ qAdvS = .act src (.move .right) qCheck)
    (pre word : List Bool) (s0 : ℤ) (_hs0 : 0 ≤ s0)
    (t : LCfg R₁.tapeCount R₂.tapeCount) (p l u : LPos R₁.tapeCount R₂.tapeCount) (L_env U_env : ℤ)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r) (henv : ∀ r, L_env ≤ l r ∧ u r ≤ U_env)
    (hs_env : s0 + (word.length : ℤ) ≤ U_env)
    (hd_env : ((pre.length + word.length : ℕ) : ℤ) ≤ U_env)
    (hpS : p src = s0) (hpD : p dst = pre.length)
    (htS : ∀ z : ℤ, s0 ≤ z → absCell (t src) s0 z =
      if h : (z - s0).toNat < word.length then some word[(z - s0).toNat] else none)
    (htD : IsWordAt (t dst) (pre.length : ℤ) pre) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qCheck) t p l u)
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qNext) t1 p1 l1 u1) ∧
      n = 4 * word.length + 1 ∧
      (∀ r, r ≠ src → r ≠ dst → t1 r = t r ∧ p1 r = p r ∧ l1 r = l r ∧ u1 r = u r) ∧
      (∀ z : ℤ, absCell (t1 src) (s0 + (word.length : ℤ)) z = absCell (t src) s0 z) ∧
      p1 src = s0 + (word.length : ℤ) ∧
      IsWordAt (t1 dst) ((pre.length + word.length : ℕ) : ℤ) (pre ++ word) ∧
      p1 dst = ((pre.length + word.length : ℕ) : ℤ) ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) := by
  let ts0 := t src
  have ind : ∀ (rem k : ℕ) (_hk : k ≤ word.length) (_hrem : word.length - k = rem)
      (t' : LCfg R₁.tapeCount R₂.tapeCount) (p' l' u' : LPos R₁.tapeCount R₂.tapeCount)
      (hw' : ∀ r, l' r ≤ p' r ∧ p' r ≤ u' r) (henv' : ∀ r, L_env ≤ l' r ∧ u' r ≤ U_env)
      (hpS' : p' src = s0 + (k : ℤ)) (hpD' : p' dst = ((pre.length + k : ℕ) : ℤ))
      (htS' : ∀ z : ℤ, absCell (t' src) (s0 + (k : ℤ)) z = absCell ts0 s0 z)
      (htD' : IsWordAt (t' dst) ((pre.length + k : ℕ) : ℤ) (pre ++ word.take k)),
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qCheck) t' p' l' u')
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qNext) t1 p1 l1 u1) ∧
        n = 4 * rem + 1 ∧
        (∀ r, r ≠ src → r ≠ dst → t1 r = t' r ∧ p1 r = p' r ∧ l1 r = l' r ∧ u1 r = u' r) ∧
        (∀ z : ℤ, absCell (t1 src) (s0 + (word.length : ℤ)) z = absCell ts0 s0 z) ∧
        p1 src = s0 + (word.length : ℤ) ∧
        IsWordAt (t1 dst) ((pre.length + word.length : ℕ) : ℤ) (pre ++ word) ∧
        p1 dst = ((pre.length + word.length : ℕ) : ℤ) ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) := by
    intro rem
    induction rem with
    | zero =>
      intro k hk hrem t' p' l' u' hw' henv' hpS' hpD' htS' htD'
      have hkeq : k = word.length := by omega
      subst hkeq
      have hhead : (t' src).head = none := by
        rw [← absCell_self (t' src) (p' src), hpS', htS', htS _ (by omega)]
        rw [dif_neg (by omega)]
      have hs := lStep_branch R₁ R₂ (q := qCheck) (k := src) h1 t' p' l' u' (hw' src)
      rw [hhead] at hs
      exact ⟨t', p', l', u', 1, .cons hs (.refl _), rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩,
        htS', hpS', by simpa using htD', hpD', hw', henv'⟩
    | succ rem ih =>
      intro k hk hrem t' p' l' u' hw' henv' hpS' hpD' htS' htD'
      have hlt : k < word.length := by omega
      let b := word[k]
      have hhead : (t' src).head = some b := by
        rw [← absCell_self (t' src) (p' src), hpS', htS', htS _ (by omega)]
        have hc : (s0 + (k : ℤ) - s0).toNat < word.length := by simpa
        rw [dif_pos hc]; simp [b]
      have hs0 := lStep_branch R₁ R₂ (q := qCheck) (k := src) h1 t' p' l' u' (hw' src)
      rw [hhead] at hs0
      have hs1 : locatedStep (loopMachine R₁ R₂)
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (match some b with
            | none => qNext | some true => qWT | some false => qWF)) t' p' l' u') =
          some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qAdvD)
            (Function.update t' dst ((t' dst).write (some b))) p' l' u') := by
        cases hb : b
        · simpa [hb] using lStep_write R₁ R₂ h3 t' p' l' u' (hw' dst)
        · simpa [hb] using lStep_write R₁ R₂ h2 t' p' l' u' (hw' dst)
      let t_1 := Function.update t' dst ((t' dst).write (some b))
      have hs2 := lStep_move_right R₁ R₂ h4 t_1 p' l' u'
      let t_2 := Function.update t_1 dst ((t_1 dst).move .right)
      let p_2 := Function.update p' dst (p' dst + 1)
      let l_2 := Function.update l' dst (min (l' dst) (p' dst + 1))
      let u_2 := Function.update u' dst (max (u' dst) (p' dst + 1))
      have hs3 := lStep_move_right R₁ R₂ h5 t_2 p_2 l_2 u_2
      let t_3 := Function.update t_2 src ((t_2 src).move .right)
      let p_3 := Function.update p_2 src (p_2 src + 1)
      let l_3 := Function.update l_2 src (min (l_2 src) (p_2 src + 1))
      let u_3 := Function.update u_2 src (max (u_2 src) (p_2 src + 1))
      have hp3S : p_3 src = s0 + ((k + 1 : ℕ) : ℤ) := by
        dsimp [p_3, p_2]; rw [Function.update_self, Function.update_of_ne hne, hpS']; omega
      have hp3D : p_3 dst = ((pre.length + (k + 1) : ℕ) : ℤ) := by
        dsimp [p_3, p_2]; rw [Function.update_of_ne hne.symm, Function.update_self, hpD']; omega
      have hw3 : ∀ r, l_3 r ≤ p_3 r ∧ p_3 r ≤ u_3 r := by
        intro r
        by_cases hrs : r = src
        · subst r; simp only [p_3, l_3, u_3, Function.update_self]; exact ⟨min_le_right _ _, le_max_right _ _⟩
        · by_cases hrd : r = dst
          · subst r; simp only [p_3, p_2, l_3, l_2, u_3, u_2, Function.update_of_ne hrs, Function.update_self]
            exact ⟨min_le_right _ _, le_max_right _ _⟩
          · simp only [p_3, p_2, l_3, l_2, u_3, u_2, Function.update_of_ne hrs, Function.update_of_ne hrd]
            exact hw' r
      have henv3 : ∀ r, L_env ≤ l_3 r ∧ u_3 r ≤ U_env := by
        intro r
        by_cases hrs : r = src
        · subst r; have h1' := henv' src
          simp only [l_3, u_3, l_2, u_2, p_2, Function.update_self, Function.update_of_ne hne, hpS']
          exact ⟨le_min h1'.1 (by have := (hw' src).1; omega), max_le h1'.2 (by omega)⟩
        · by_cases hrd : r = dst
          · subst r; have h1' := henv' dst
            simp only [l_3, u_3, l_2, u_2, Function.update_of_ne hrs, Function.update_self, hpD']
            exact ⟨le_min h1'.1 (by have := (hw' dst).1; omega), max_le h1'.2 (by omega)⟩
          · simp only [l_3, l_2, u_3, u_2, Function.update_of_ne hrs, Function.update_of_ne hrd]
            exact henv' r
      have htS3 : ∀ z : ℤ, absCell (t_3 src) (s0 + ((k + 1 : ℕ) : ℤ)) z = absCell ts0 s0 z := by
        intro z
        have heq : t_3 src = (t' src).move .right := by
          dsimp [t_3, t_2, t_1]; rw [Function.update_self, Function.update_of_ne hne, Function.update_of_ne hne]
        rw [heq, show s0 + ((k + 1 : ℕ) : ℤ) = (s0 + (k : ℤ)) + 1 by omega, absCell_move_right, htS' z]
      have htD3 : IsWordAt (t_3 dst) ((pre.length + (k + 1) : ℕ) : ℤ) (pre ++ word.take (k + 1)) := by
        intro z
        have heq : t_3 dst = ((t' dst).write (some b)).move .right := by
          dsimp [t_3, t_2, t_1]; rw [Function.update_of_ne hne.symm, Function.update_self, Function.update_self]
        rw [heq, show ((pre.length + (k + 1) : ℕ) : ℤ) = ((pre.length + k : ℕ) : ℤ) + 1 by omega,
          absCell_move_right, absCell_write, htD' z]
        have hlen_t : (pre ++ word.take k).length = pre.length + k := by
          simp [List.length_take_of_le (by omega : k ≤ word.length)]
        have hlen_t1 : (pre ++ word.take (k + 1)).length = pre.length + k + 1 := by
          simp; omega
        by_cases hz : z = ((pre.length + k : ℕ) : ℤ)
        · subst hz
          rw [if_pos rfl, dif_pos ⟨by omega, by omega⟩]
          have hidx_eq : ((pre.length + k : ℕ) : ℤ).toNat = pre.length + k := Int.toNat_natCast _
          simp only [hidx_eq]
          have hget : (pre ++ word.take (k + 1))[pre.length + k] = b := by
            rw [List.getElem_append_right (by omega)]
            simp [List.getElem_take, b]
          exact congrArg some hget.symm
        · rw [if_neg hz]
          by_cases h0 : 0 ≤ z ∧ z.toNat < pre.length + k
          · have h0a : 0 ≤ z ∧ z.toNat < (pre ++ word.take k).length := ⟨h0.1, by omega⟩
            have h0b : 0 ≤ z ∧ z.toNat < (pre ++ word.take (k + 1)).length := ⟨h0.1, by omega⟩
            rw [dif_pos h0a, dif_pos h0b]
            by_cases hpre : z.toNat < pre.length
            · rw [List.getElem_append_left hpre, List.getElem_append_left hpre]
            · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
              simp [List.getElem_take]
          · have h0a : ¬ (0 ≤ z ∧ z.toNat < (pre ++ word.take k).length) := by omega
            have h0b : ¬ (0 ≤ z ∧ z.toNat < (pre ++ word.take (k + 1)).length) := by omega
            rw [dif_neg h0a, dif_neg h0b]
      obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hout1, htS1, hp1S, htD1, hp1D, hw1, henv1⟩ :=
        ih (k + 1) hlt (by omega) t_3 p_3 l_3 u_3 hw3 henv3 hp3S hp3D htS3 htD3
      refine ⟨t1, p1, l1, u1, 4 + n1, trace_prepend4 hs0 hs1 hs2 hs3 htail, by omega,
        ?_, htS1, hp1S, htD1, hp1D, hw1, henv1⟩
      intro r hr1 hr2
      have ho := hout1 r hr1 hr2
      simp only [t_3, t_2, t_1, p_3, p_2, l_3, l_2, u_3, u_2,
        Function.update_of_ne hr1, Function.update_of_ne hr2] at ho
      exact ho
  exact ind word.length 0 (Nat.zero_le _) (Nat.sub_zero _) t p l u hw henv
    (by simpa using hpS) (by simpa using hpD) (fun _ => by simp [ts0])
    (fun z => by simpa [IsWordAt] using htD z)

private theorem list_flatMap_pair_length (xs : List Bool) :
    (xs.flatMap (fun b => [true, b])).length = 2 * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

private theorem list_flatMap_pair_even (xs : List Bool) {k : ℕ} (hk : k < xs.length) :
    (xs.flatMap (fun b => [true, b]))[2 * k]'(by rw [list_flatMap_pair_length]; omega) = true := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    simp only [List.length_cons] at hk
    cases k with
    | zero => simp
    | succ k => simp [Nat.mul_add]; exact ih (by omega)

private theorem list_flatMap_pair_odd (xs : List Bool) {k : ℕ} (hk : k < xs.length) :
    (xs.flatMap (fun b => [true, b]))[2 * k + 1]'(by rw [list_flatMap_pair_length]; omega) = xs[k] := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    simp only [List.length_cons] at hk
    cases k with
    | zero => simp
    | succ k => simp [Nat.mul_add]; exact ih (by omega)

private theorem lPhase_encPairs (st : List Bool)
    (t : LCfg R₁.tapeCount R₂.tapeCount) (p l u : LPos R₁.tapeCount R₂.tapeCount) (L_env U_env : ℤ)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r) (henv : ∀ r, L_env ≤ l r ∧ u r ≤ U_env)
    (hSt_env : (st.length : ℤ) ≤ U_env)
    (hR1_env : ((2 * st.length + 1 : ℕ) : ℤ) ≤ U_env)
    (hpSt : p tSt = 0) (hpR1 : p (tR1 R₁.inputTape) = 0)
    (htSt : IsWordAt (t tSt) 0 st) (htR1 : t (tR1 R₁.inputTape) = Turing.Tape.mk₁ []) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qEncStCheck) t p l u)
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qEncAnsCheck) t1 p1 l1 u1) ∧
      n = 6 * st.length + 3 ∧
      (∀ r, r ≠ tSt → r ≠ tR1 R₁.inputTape → t1 r = t r ∧ p1 r = p r ∧ l1 r = l r ∧ u1 r = u r) ∧
      IsWordAt (t1 tSt) (st.length : ℤ) st ∧ p1 tSt = st.length ∧
      IsWordAt (t1 (tR1 R₁.inputTape)) ((2 * st.length + 1 : ℕ) : ℤ)
        (st.flatMap (fun b => [true, b]) ++ [false]) ∧
      p1 (tR1 R₁.inputTape) = ((2 * st.length + 1 : ℕ) : ℤ) ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) := by
  let dst : LTape R₁.tapeCount R₂.tapeCount := tR1 R₁.inputTape
  have hne : (tSt : LTape R₁.tapeCount R₂.tapeCount) ≠ dst := by simp [dst]
  have ind : ∀ (rem k : ℕ) (_hk : k ≤ st.length) (_hrem : st.length - k = rem)
      (t' : LCfg R₁.tapeCount R₂.tapeCount) (p' l' u' : LPos R₁.tapeCount R₂.tapeCount)
      (hw' : ∀ r, l' r ≤ p' r ∧ p' r ≤ u' r) (henv' : ∀ r, L_env ≤ l' r ∧ u' r ≤ U_env)
      (hpSt' : p' tSt = k) (hpR1' : p' dst = ((2 * k : ℕ) : ℤ))
      (htSt' : IsWordAt (t' tSt) (k : ℤ) st)
      (htR1' : IsWordAt (t' dst) ((2 * k : ℕ) : ℤ) ((st.take k).flatMap (fun b => [true, b]))),
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qEncStCheck) t' p' l' u')
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qEncAnsCheck) t1 p1 l1 u1) ∧
        n = 6 * rem + 3 ∧
        (∀ r, r ≠ tSt → r ≠ dst → t1 r = t' r ∧ p1 r = p' r ∧ l1 r = l' r ∧ u1 r = u' r) ∧
        IsWordAt (t1 tSt) (st.length : ℤ) st ∧ p1 tSt = st.length ∧
        IsWordAt (t1 dst) ((2 * st.length + 1 : ℕ) : ℤ)
          (st.flatMap (fun b => [true, b]) ++ [false]) ∧
        p1 dst = ((2 * st.length + 1 : ℕ) : ℤ) ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) := by
    intro rem
    induction rem with
    | zero =>
      intro k hk hrem t' p' l' u' hw' henv' hpSt' hpR1' htSt' htR1'
      have hkeq : k = st.length := by omega
      subst hkeq
      have hhead : (t' tSt).head = none := by
        rw [← absCell_self (t' tSt) (p' tSt), hpSt', htSt']; simp
      have hs0 := lStep_branch R₁ R₂ (q := qEncStCheck) (k := tSt) (by rfl) t' p' l' u' (hw' tSt)
      rw [hhead] at hs0
      have hs1 := lStep_write R₁ R₂ (q := qEncSep) (q' := qEncSepAdv) (k := dst) (sym := some false)
        (by rfl) t' p' l' u' (hw' dst)
      let t_1 := Function.update t' dst ((t' dst).write (some false))
      have hs2 := lStep_move_right R₁ R₂ (q := qEncSepAdv) (q' := qEncAnsCheck) (k := dst)
        (by rfl) t_1 p' l' u'
      let t_2 := Function.update t_1 dst ((t_1 dst).move .right)
      let p_2 := Function.update p' dst (p' dst + 1)
      let l_2 := Function.update l' dst (min (l' dst) (p' dst + 1))
      let u_2 := Function.update u' dst (max (u' dst) (p' dst + 1))
      refine ⟨t_2, p_2, l_2, u_2, 3, .cons hs0 (.cons hs1 (.cons hs2 (.refl _))), rfl,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro r hr1 hr2
        dsimp [t_2, t_1, p_2, l_2, u_2]; simp [hr2]
      · have heq : t_2 tSt = t' tSt := by simp [t_2, t_1, hne]
        rw [heq]; exact htSt'
      · simp [p_2, hne, hpSt']
      · intro z
        have heq : t_2 dst = ((t' dst).write (some false)).move .right := by simp [t_2, t_1]
        rw [heq, show ((2 * st.length + 1 : ℕ) : ℤ) = ((2 * st.length : ℕ) : ℤ) + 1 by omega,
          absCell_move_right, absCell_write]
        have htake : st.take st.length = st := List.take_length
        rw [htake] at htR1'
        rw [htR1' z]
        have hlen1 : (st.flatMap (fun b => [true, b])).length = 2 * st.length :=
          list_flatMap_pair_length st
        have hlen2 : (st.flatMap (fun b => [true, b]) ++ [false]).length = 2 * st.length + 1 := by
          simp [hlen1]
        by_cases hz : z = ((2 * st.length : ℕ) : ℤ)
        · subst z; rw [if_pos rfl, dif_pos ⟨by omega, by omega⟩]
          have hidx_eq : ((2 * st.length : ℕ) : ℤ).toNat = 2 * st.length := Int.toNat_natCast _
          simp only [hidx_eq]
          have hget : (st.flatMap (fun b => [true, b]) ++ [false])[2 * st.length] = false := by
            rw [List.getElem_append_right (by simp [hlen1])]; simp [hlen1]
          exact congrArg some hget.symm
        · rw [if_neg hz]
          by_cases h0 : 0 ≤ z ∧ z.toNat < 2 * st.length
          · rw [dif_pos ⟨h0.1, by omega⟩, dif_pos ⟨h0.1, by omega⟩]
            simp [List.getElem_append_left (by omega : z.toNat < (st.flatMap (fun b => [true, b])).length)]
          · rw [dif_neg (by omega), dif_neg (by omega)]
      · simp [p_2, hpR1']
      · intro r; by_cases hr : r = dst
        · subst r; simp only [p_2, l_2, u_2, Function.update_self]; exact ⟨min_le_right _ _, le_max_right _ _⟩
        · simp only [p_2, l_2, u_2, Function.update_of_ne hr]; exact hw' r
      · intro r; by_cases hr : r = dst
        · subst r; have h1' := henv' dst
          simp only [l_2, u_2, Function.update_self, hpR1']
          exact ⟨le_min h1'.1 (by have := (hw' dst).1; omega), max_le h1'.2 (by omega)⟩
        · simp only [l_2, u_2, Function.update_of_ne hr]; exact henv' r
    | succ rem ih =>
      intro k hk hrem t' p' l' u' hw' henv' hpSt' hpR1' htSt' htR1'
      have hlt : k < st.length := by omega
      let b := st[k]
      have hhead : (t' tSt).head = some b := by
        rw [← absCell_self (t' tSt) (p' tSt), hpSt', htSt']
        rw [dif_pos ⟨Int.natCast_nonneg k, by simpa⟩]; simp [b]
      have hs0 := lStep_branch R₁ R₂ (q := qEncStCheck) (k := tSt) (by rfl) t' p' l' u' (hw' tSt)
      rw [hhead] at hs0
      have hs1 : locatedStep (loopMachine R₁ R₂)
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (match some b with
            | none => qEncSep | some true => qEncStW1T | some false => qEncStW1F)) t' p' l' u') =
          some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (if b then qEncStAdv1T else qEncStAdv1F))
            (Function.update t' dst ((t' dst).write (some true))) p' l' u') := by
        cases hb : b
        · simpa [hb] using lStep_write R₁ R₂ (q := qEncStW1F) (q' := qEncStAdv1F)
            (k := dst) (sym := some true) (by rfl) t' p' l' u' (hw' dst)
        · simpa [hb] using lStep_write R₁ R₂ (q := qEncStW1T) (q' := qEncStAdv1T)
            (k := dst) (sym := some true) (by rfl) t' p' l' u' (hw' dst)
      let t_1 := Function.update t' dst ((t' dst).write (some true))
      have hs2 : locatedStep (loopMachine R₁ R₂)
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (if b then qEncStAdv1T else qEncStAdv1F)) t_1 p' l' u') =
          some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (if b then qEncStW2T else qEncStW2F))
            (Function.update t_1 dst ((t_1 dst).move .right))
            (Function.update p' dst (p' dst + 1))
            (Function.update l' dst (min (l' dst) (p' dst + 1)))
            (Function.update u' dst (max (u' dst) (p' dst + 1)))) := by
        cases hb : b
        · simpa [hb] using lStep_move_right R₁ R₂ (q := qEncStAdv1F) (q' := qEncStW2F)
            (k := dst) (by rfl) t_1 p' l' u'
        · simpa [hb] using lStep_move_right R₁ R₂ (q := qEncStAdv1T) (q' := qEncStW2T)
            (k := dst) (by rfl) t_1 p' l' u'
      let t_2 := Function.update t_1 dst ((t_1 dst).move .right)
      let p_2 := Function.update p' dst (p' dst + 1)
      let l_2 := Function.update l' dst (min (l' dst) (p' dst + 1))
      let u_2 := Function.update u' dst (max (u' dst) (p' dst + 1))
      have hw2_dst : l_2 dst ≤ p_2 dst ∧ p_2 dst ≤ u_2 dst := by simp only [l_2, p_2, u_2, Function.update_self]; exact ⟨min_le_right _ _, le_max_right _ _⟩
      have hs3 : locatedStep (loopMachine R₁ R₂)
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (if b then qEncStW2T else qEncStW2F)) t_2 p_2 l_2 u_2) =
          some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qEncStAdv2)
            (Function.update t_2 dst ((t_2 dst).write (some b))) p_2 l_2 u_2) := by
        cases hb : b
        · simpa [hb] using lStep_write R₁ R₂ (q := qEncStW2F) (q' := qEncStAdv2)
            (k := dst) (sym := some false) (by rfl) t_2 p_2 l_2 u_2 hw2_dst
        · simpa [hb] using lStep_write R₁ R₂ (q := qEncStW2T) (q' := qEncStAdv2)
            (k := dst) (sym := some true) (by rfl) t_2 p_2 l_2 u_2 hw2_dst
      let t_3 := Function.update t_2 dst ((t_2 dst).write (some b))
      have hs4 := lStep_move_right R₁ R₂ (q := qEncStAdv2) (q' := qEncStAdvSrc) (k := dst)
        (by rfl) t_3 p_2 l_2 u_2
      let t_4 := Function.update t_3 dst ((t_3 dst).move .right)
      let p_4 := Function.update p_2 dst (p_2 dst + 1)
      let l_4 := Function.update l_2 dst (min (l_2 dst) (p_2 dst + 1))
      let u_4 := Function.update u_2 dst (max (u_2 dst) (p_2 dst + 1))
      have hs5 := lStep_move_right R₁ R₂ (q := qEncStAdvSrc) (q' := qEncStCheck) (k := tSt)
        (by rfl) t_4 p_4 l_4 u_4
      let t_5 := Function.update t_4 tSt ((t_4 tSt).move .right)
      let p_5 := Function.update p_4 tSt (p_4 tSt + 1)
      let l_5 := Function.update l_4 tSt (min (l_4 tSt) (p_4 tSt + 1))
      let u_5 := Function.update u_4 tSt (max (u_4 tSt) (p_4 tSt + 1))
      have hp5St : p_5 tSt = ((k + 1 : ℕ) : ℤ) := by
        dsimp [p_5, p_4, p_2]; rw [Function.update_self, Function.update_of_ne hne, Function.update_of_ne hne, hpSt']
      have hp5R1 : p_5 dst = ((2 * (k + 1) : ℕ) : ℤ) := by
        dsimp [p_5, p_4, p_2]; rw [Function.update_of_ne hne.symm, Function.update_self, Function.update_self, hpR1']; omega
      have hw5 : ∀ r, l_5 r ≤ p_5 r ∧ p_5 r ≤ u_5 r := by
        intro r
        by_cases hrs : r = tSt
        · subst r; simp only [p_5, l_5, u_5, Function.update_self]; exact ⟨min_le_right _ _, le_max_right _ _⟩
        · by_cases hrd : r = dst
          · subst r; simp only [p_5, p_4, l_5, l_4, u_5, u_4, Function.update_of_ne hrs, Function.update_self]
            exact ⟨min_le_right _ _, le_max_right _ _⟩
          · simp only [p_5, p_4, p_2, l_5, l_4, l_2, u_5, u_4, u_2, Function.update_of_ne hrs, Function.update_of_ne hrd]
            exact hw' r
      have henv5 : ∀ r, L_env ≤ l_5 r ∧ u_5 r ≤ U_env := by
        intro r
        by_cases hrs : r = tSt
        · subst r; have h1' := henv' tSt
          simp only [l_5, u_5, l_4, l_2, u_4, u_2, p_4, p_2, Function.update_self, Function.update_of_ne hne, hpSt']
          exact ⟨le_min h1'.1 (by have := (hw' tSt).1; omega), max_le h1'.2 (by omega)⟩
        · by_cases hrd : r = dst
          · subst r; have h1' := henv' dst
            have hlo : l_5 dst = min (min (l' dst) (p' dst + 1)) (p' dst + 1 + 1) := by
              dsimp [l_5, l_4, l_2, p_2]; rw [Function.update_of_ne hne.symm, Function.update_self, Function.update_self, Function.update_self]
            have hhi : u_5 dst = max (max (u' dst) (p' dst + 1)) (p' dst + 1 + 1) := by
              dsimp [u_5, u_4, u_2, p_2]; rw [Function.update_of_ne hne.symm, Function.update_self, Function.update_self, Function.update_self]
            rw [hlo, hhi, hpR1']
            exact ⟨le_min (le_min h1'.1 (by have := (hw' dst).1; omega)) (by have := (hw' dst).1; omega),
                   max_le (max_le h1'.2 (by omega)) (by omega)⟩
          · simp only [l_5, l_4, l_2, u_5, u_4, u_2, Function.update_of_ne hrs, Function.update_of_ne hrd]
            exact henv' r
      have htSt5 : IsWordAt (t_5 tSt) ((k + 1 : ℕ) : ℤ) st := by
        intro z
        have heq : t_5 tSt = (t' tSt).move .right := by
          dsimp [t_5, t_4, t_3, t_2, t_1]
          rw [Function.update_self, Function.update_of_ne hne, Function.update_of_ne hne,
              Function.update_of_ne hne, Function.update_of_ne hne]
        rw [heq, show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by omega, absCell_move_right, htSt' z]
      have htR1_5 : IsWordAt (t_5 dst) ((2 * (k + 1) : ℕ) : ℤ) ((st.take (k + 1)).flatMap (fun b => [true, b])) := by
        intro z
        have heq : t_5 dst = ((((t' dst).write (some true)).move .right).write (some b)).move .right := by
          dsimp [t_5, t_4, t_3, t_2, t_1]
          rw [Function.update_of_ne hne.symm, Function.update_self, Function.update_self, Function.update_self, Function.update_self]
        rw [heq, show ((2 * (k + 1) : ℕ) : ℤ) = ((2 * k : ℕ) : ℤ) + 1 + 1 by omega,
          absCell_move_right, absCell_write, absCell_move_right, absCell_write, htR1' z]
        have htak : st.take (k + 1) = st.take k ++ [b] := List.take_succ_eq_append_getElem hlt
        have hflat : (st.take (k + 1)).flatMap (fun x => [true, x]) =
            (st.take k).flatMap (fun x => [true, x]) ++ [true, b] := by
          rw [htak, List.flatMap_append]; simp
        have hlen0 : ((st.take k).flatMap (fun x => [true, x])).length = 2 * k := by
          rw [list_flatMap_pair_length, List.length_take_of_le (by omega)]
        have hlen1' : ((st.take k).flatMap (fun x => [true, x]) ++ [true, b]).length = 2 * k + 2 := by
          rw [List.length_append, hlen0]; simp
        have hlen1 : ((st.take (k + 1)).flatMap (fun x => [true, x])).length = 2 * k + 2 := by
          rw [hflat]; exact hlen1'
        rw [hflat]
        by_cases hz1 : z = ((2 * k : ℕ) : ℤ) + 1
        · subst z
          rw [if_pos rfl, dif_pos ⟨by omega, by omega⟩]
          have hidx1 : (((2 * k : ℕ) : ℤ) + 1).toNat = 2 * k + 1 := by omega
          simp only [hidx1]
          have hg : ((st.take k).flatMap (fun x => [true, x]) ++ [true, b])[2 * k + 1]'(by omega) = b := by
            rw [List.getElem_append_right (by omega)]; simp [hlen0]
          exact congrArg some hg.symm
        · rw [if_neg hz1]
          by_cases hz0 : z = ((2 * k : ℕ) : ℤ)
          · subst z
            rw [if_pos rfl, dif_pos ⟨by omega, by omega⟩]
            have hidx0 : ((2 * k : ℕ) : ℤ).toNat = 2 * k := Int.toNat_natCast _
            simp only [hidx0]
            have hg : ((st.take k).flatMap (fun x => [true, x]) ++ [true, b])[2 * k]'(by omega) = true := by
              rw [List.getElem_append_right (by omega)]; simp [hlen0]
            exact congrArg some hg.symm
          · rw [if_neg hz0]
            by_cases h0 : 0 ≤ z ∧ z.toNat < 2 * k
            · rw [dif_pos ⟨h0.1, by omega⟩, dif_pos ⟨h0.1, by omega⟩]
              simp [List.getElem_append_left (by omega : z.toNat < ((st.take k).flatMap (fun x => [true, x])).length)]
            · rw [dif_neg (by omega), dif_neg (by omega)]
      obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hout1, htS1, hp1S, htR1_1, hp1R1, hw1, henv1⟩ :=
        ih (k + 1) hlt (by omega) t_5 p_5 l_5 u_5 hw5 henv5 hp5St hp5R1 htSt5 htR1_5
      refine ⟨t1, p1, l1, u1, 6 + n1, trace_prepend6 hs0 hs1 hs2 hs3 hs4 hs5 htail, by omega,
        ?_, htS1, hp1S, htR1_1, hp1R1, hw1, henv1⟩
      intro r hr1 hr2
      have ho := hout1 r hr1 hr2
      simp only [t_5, t_4, t_3, t_2, t_1, p_5, p_4, p_2, l_5, l_4, l_2, u_5, u_4, u_2,
        Function.update_of_ne hr1, Function.update_of_ne hr2] at ho
      exact ho
  exact ind st.length 0 (Nat.zero_le _) (Nat.sub_zero _) t p l u hw henv
    hpSt (by simpa using hpR1) htSt (by simpa [isWordAt_zero_iff] using htR1)

private theorem absCell_mk₁_eq_none (w : List Bool) (z : ℤ) :
    absCell (Turing.Tape.mk₁ (w.map some)) 0 z = none ↔ ¬ (0 ≤ z ∧ z < (w.length : ℤ)) := by
  rw [absCell_mk₁_zero]
  split_ifs with h <;> simp <;> omega

private theorem absCell_mk₁_ne_none_of_lt (w : List Bool) {z : ℤ}
    (h0 : 0 ≤ z) (h1 : z < (w.length : ℤ)) :
    absCell (Turing.Tape.mk₁ (w.map some)) 0 z ≠ none := by
  intro h; rw [absCell_mk₁_eq_none] at h; omega

private theorem lPhase_decPairs (st' q : List Bool)
    (t : LCfg R₁.tapeCount R₂.tapeCount) (p l u : LPos R₁.tapeCount R₂.tapeCount) (L_env U_env : ℤ)
    (hw : ∀ r, l r ≤ p r ∧ p r ≤ u r) (henv : ∀ r, L_env ≤ l r ∧ u r ≤ U_env)
    (hR1_env : ((2 * st'.length + 2 : ℕ) : ℤ) ≤ U_env)
    (hSt_env : (st'.length : ℤ) ≤ U_env)
    (hpR1 : p (tR1 R₁.inputTape) = 1) (hpSt : p tSt = 0)
    (htR1 : ∀ z : ℤ, absCell (t (tR1 R₁.inputTape)) 1 z =
      absCell (Turing.Tape.mk₁ ((false :: (st'.flatMap (fun b => [true, b]) ++ [false] ++ q)).map some)) 0 z)
    (htSt : t tSt = Turing.Tape.mk₁ []) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qDecCheck1) t p l u)
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qDecQCheck) t1 p1 l1 u1) ∧
      n = 6 * st'.length + 2 ∧
      (∀ r, r ≠ tR1 R₁.inputTape → r ≠ tSt → t1 r = t r ∧ p1 r = p r ∧ l1 r = l r ∧ u1 r = u r) ∧
      (∀ z : ℤ, absCell (t1 (tR1 R₁.inputTape)) ((2 * st'.length + 2 : ℕ) : ℤ) z =
        absCell (Turing.Tape.mk₁ ((false :: (st'.flatMap (fun b => [true, b]) ++ [false] ++ q)).map some)) 0 z) ∧
      p1 (tR1 R₁.inputTape) = ((2 * st'.length + 2 : ℕ) : ℤ) ∧
      IsWordAt (t1 tSt) (st'.length : ℤ) st' ∧
      p1 tSt = st'.length ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) := by
  let src : LTape R₁.tapeCount R₂.tapeCount := tR1 R₁.inputTape
  let ts0 := t src
  have hne : (src : LTape R₁.tapeCount R₂.tapeCount) ≠ tSt := by simp [src]
  let fw := false :: (st'.flatMap (fun b => [true, b]) ++ [false] ++ q)
  have hfw_len : fw.length = 1 + 2 * st'.length + 1 + q.length := by
    dsimp [fw]; rw [List.length_append, List.length_append, List.length_singleton,
      list_flatMap_pair_length]; omega
  have ind : ∀ (rem k : ℕ) (_hk : k ≤ st'.length) (_hrem : st'.length - k = rem)
      (t' : LCfg R₁.tapeCount R₂.tapeCount) (p' l' u' : LPos R₁.tapeCount R₂.tapeCount)
      (hw' : ∀ r, l' r ≤ p' r ∧ p' r ≤ u' r) (henv' : ∀ r, L_env ≤ l' r ∧ u' r ≤ U_env)
      (hpR1' : p' src = ((1 + 2 * k : ℕ) : ℤ)) (hpSt' : p' tSt = k)
      (htR1' : ∀ z : ℤ, absCell (t' src) ((1 + 2 * k : ℕ) : ℤ) z = absCell ts0 1 z)
      (htSt' : IsWordAt (t' tSt) (k : ℤ) (st'.take k)),
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qDecCheck1) t' p' l' u')
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qDecQCheck) t1 p1 l1 u1) ∧
        n = 6 * rem + 2 ∧
        (∀ r, r ≠ src → r ≠ tSt → t1 r = t' r ∧ p1 r = p' r ∧ l1 r = l' r ∧ u1 r = u' r) ∧
        (∀ z : ℤ, absCell (t1 src) ((2 * st'.length + 2 : ℕ) : ℤ) z = absCell ts0 1 z) ∧
        p1 src = ((2 * st'.length + 2 : ℕ) : ℤ) ∧
        IsWordAt (t1 tSt) (st'.length : ℤ) st' ∧
        p1 tSt = st'.length ∧
        (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) := by
    intro rem
    induction rem with
    | zero =>
      intro k hk hrem t' p' l' u' hw' henv' hpR1' hpSt' htR1' htSt'
      have hkeq : k = st'.length := by omega
      subst hkeq
      have hidx : 2 * st'.length + 1 < fw.length := by rw [hfw_len]; omega
      have hget : fw[2 * st'.length + 1] = false := by
        have hl : (st'.flatMap (fun b => [true, b])).length = 2 * st'.length :=
          list_flatMap_pair_length st'
        have hlt1 : 2 * st'.length < (st'.flatMap (fun b => [true, b]) ++ [false]).length := by
          rw [List.length_append, hl, List.length_singleton]; omega
        dsimp [fw]
        rw [List.getElem_append_left hlt1, List.getElem_append_right hl.le]
        simp [hl]
      have hz_nat : ((1 + 2 * st'.length : ℕ) : ℤ).toNat = 2 * st'.length + 1 := by omega
      have hhead : (t' src).head = some false := by
        rw [← absCell_self (t' src) (p' src), hpR1', htR1', htR1,
          show (false :: (st'.flatMap (fun b => [true, b]) ++ [false] ++ q)) = fw from rfl,
          absCell_mk₁_zero, dif_pos ⟨by omega, by rw [hz_nat]; exact hidx⟩]
        simp only [hz_nat, hget]
      have hs0 := lStep_branch R₁ R₂ (q := qDecCheck1) (k := src) (by rfl) t' p' l' u' (hw' src)
      rw [hhead] at hs0
      have hs1 := lStep_move_right R₁ R₂ (q := qDecSepAdv) (q' := qDecQCheck) (k := src)
        (by rfl) t' p' l' u'
      let t_1 := Function.update t' src ((t' src).move .right)
      let p_1 := Function.update p' src (p' src + 1)
      let l_1 := Function.update l' src (min (l' src) (p' src + 1))
      let u_1 := Function.update u' src (max (u' src) (p' src + 1))
      refine ⟨t_1, p_1, l_1, u_1, 2, .cons hs0 (.cons hs1 (.refl _)), rfl,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro r hr1 _
        dsimp [t_1, p_1, l_1, u_1]; simp [hr1]
      · intro z
        have heq : t_1 src = (t' src).move .right := by simp [t_1]
        rw [heq, show ((2 * st'.length + 2 : ℕ) : ℤ) = ((1 + 2 * st'.length : ℕ) : ℤ) + 1 by omega,
          absCell_move_right, htR1' z]
      · simp [p_1, hpR1']; omega
      · have heq : t_1 tSt = t' tSt := by simp [t_1, hne.symm]
        rw [heq]; simpa using htSt'
      · simp [p_1, hne.symm, hpSt']
      · intro r; by_cases hr : r = src
        · subst r; simp only [p_1, l_1, u_1, Function.update_self]; exact ⟨min_le_right _ _, le_max_right _ _⟩
        · simp only [p_1, l_1, u_1, Function.update_of_ne hr]; exact hw' r
      · intro r; by_cases hr : r = src
        · subst r; have h1' := henv' src; simp only [l_1, u_1, Function.update_self, hpR1']
          exact ⟨le_min h1'.1 (by have := (hw' src).1; omega), max_le h1'.2 (by omega)⟩
        · simp only [l_1, u_1, Function.update_of_ne hr]; exact henv' r
    | succ rem ih =>
      intro k hk hrem t' p' l' u' hw' henv' hpR1' hpSt' htR1' htSt'
      have hlt : k < st'.length := by omega
      have hidx0 : 2 * k + 1 < fw.length := by rw [hfw_len]; omega
      have hget0 : fw[2 * k + 1] = true := by
        dsimp [fw]
        rw [List.getElem_append_left (by rw [List.length_append, list_flatMap_pair_length]; omega),
          List.getElem_append_left (by rw [list_flatMap_pair_length]; omega)]
        exact list_flatMap_pair_even st' hlt
      have hz0 : ((1 + 2 * k : ℕ) : ℤ).toNat = 2 * k + 1 := by omega
      have hhead0 : (t' src).head = some true := by
        rw [← absCell_self (t' src) (p' src), hpR1', htR1', htR1,
          show (false :: (st'.flatMap (fun b => [true, b]) ++ [false] ++ q)) = fw from rfl,
          absCell_mk₁_zero, dif_pos ⟨by omega, by rw [hz0]; exact hidx0⟩]
        simp only [hz0, hget0]
      have hs0 := lStep_branch R₁ R₂ (q := qDecCheck1) (k := src) (by rfl) t' p' l' u' (hw' src)
      rw [hhead0] at hs0
      have hs1 := lStep_move_right R₁ R₂ (q := qDecAdv1) (q' := qDecBit) (k := src)
        (by rfl) t' p' l' u'
      let t_1 := Function.update t' src ((t' src).move .right)
      let p_1 := Function.update p' src (p' src + 1)
      let l_1 := Function.update l' src (min (l' src) (p' src + 1))
      let u_1 := Function.update u' src (max (u' src) (p' src + 1))
      have hp1S : p_1 src = ((1 + 2 * k + 1 : ℕ) : ℤ) := by simp [p_1, hpR1']
      have ht1S : ∀ z : ℤ, absCell (t_1 src) ((1 + 2 * k + 1 : ℕ) : ℤ) z = absCell ts0 1 z := by
        intro z
        rw [show t_1 src = (t' src).move .right from by simp [t_1],
          show ((1 + 2 * k + 1 : ℕ) : ℤ) = ((1 + 2 * k : ℕ) : ℤ) + 1 by omega,
          absCell_move_right, htR1' z]
      let b := st'[k]
      have hidx1 : (2 * k + 1) + 1 < fw.length := by rw [hfw_len]; omega
      have hget1 : fw[(2 * k + 1) + 1] = b := by
        dsimp [fw, b]
        rw [List.getElem_append_left (by rw [List.length_append, list_flatMap_pair_length]; omega),
          List.getElem_append_left (by rw [list_flatMap_pair_length]; omega)]
        exact list_flatMap_pair_odd st' hlt
      have hz1 : ((1 + 2 * k + 1 : ℕ) : ℤ).toNat = (2 * k + 1) + 1 := by omega
      have hhead1 : (t_1 src).head = some b := by
        rw [← absCell_self (t_1 src) (p_1 src), hp1S, ht1S, htR1,
          show (false :: (st'.flatMap (fun b => [true, b]) ++ [false] ++ q)) = fw from rfl,
          absCell_mk₁_zero, dif_pos ⟨by omega, by rw [hz1]; exact hidx1⟩]
        simp only [hz1, hget1]
      have hw1_src : l_1 src ≤ p_1 src ∧ p_1 src ≤ u_1 src := by
        simp only [p_1, l_1, u_1, Function.update_self]; exact ⟨min_le_right _ _, le_max_right _ _⟩
      have hw1_st : l_1 tSt ≤ p_1 tSt ∧ p_1 tSt ≤ u_1 tSt := by
        simp only [p_1, l_1, u_1, Function.update_of_ne hne.symm]; exact hw' tSt
      have hs2 := lStep_branch R₁ R₂ (q := qDecBit) (k := src) (by rfl) t_1 p_1 l_1 u_1 hw1_src
      rw [hhead1] at hs2
      have hs3 : locatedStep (loopMachine R₁ R₂)
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (match some b with
            | some true => qDecStWT | some false => qDecStWF | none => qDecStWT)) t_1 p_1 l_1 u_1) =
          some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qDecAdvSt)
            (Function.update t_1 tSt ((t_1 tSt).write (some b))) p_1 l_1 u_1) := by
        cases hb : b
        · simpa [hb] using lStep_write R₁ R₂ (q := qDecStWF) (q' := qDecAdvSt) (k := tSt) (sym := some false)
            (by rfl) t_1 p_1 l_1 u_1 hw1_st
        · simpa [hb] using lStep_write R₁ R₂ (q := qDecStWT) (q' := qDecAdvSt) (k := tSt) (sym := some true)
            (by rfl) t_1 p_1 l_1 u_1 hw1_st
      let t_3 := Function.update t_1 tSt ((t_1 tSt).write (some b))
      have hs4 := lStep_move_right R₁ R₂ (q := qDecAdvSt) (q' := qDecAdv2) (k := tSt)
        (by rfl) t_3 p_1 l_1 u_1
      let t_4 := Function.update t_3 tSt ((t_3 tSt).move .right)
      let p_4 := Function.update p_1 tSt (p_1 tSt + 1)
      let l_4 := Function.update l_1 tSt (min (l_1 tSt) (p_1 tSt + 1))
      let u_4 := Function.update u_1 tSt (max (u_1 tSt) (p_1 tSt + 1))
      have hs5 := lStep_move_right R₁ R₂ (q := qDecAdv2) (q' := qDecCheck1) (k := src)
        (by rfl) t_4 p_4 l_4 u_4
      let t_5 := Function.update t_4 src ((t_4 src).move .right)
      let p_5 := Function.update p_4 src (p_4 src + 1)
      let l_5 := Function.update l_4 src (min (l_4 src) (p_4 src + 1))
      let u_5 := Function.update u_4 src (max (u_4 src) (p_4 src + 1))
      have hp5R1 : p_5 src = ((1 + 2 * (k + 1) : ℕ) : ℤ) := by
        dsimp [p_5, p_4, p_1]; rw [Function.update_self, Function.update_of_ne hne, Function.update_self, hpR1']; omega
      have hp5St : p_5 tSt = ((k + 1 : ℕ) : ℤ) := by
        dsimp [p_5, p_4, p_1]; rw [Function.update_of_ne hne.symm, Function.update_self, Function.update_of_ne hne.symm, hpSt']
      have hw5 : ∀ r, l_5 r ≤ p_5 r ∧ p_5 r ≤ u_5 r := by
        intro r
        by_cases hrs : r = src
        · subst r; simp only [p_5, l_5, u_5, Function.update_self]; exact ⟨min_le_right _ _, le_max_right _ _⟩
        · by_cases hrt : r = tSt
          · subst r; simp only [p_5, p_4, l_5, l_4, u_5, u_4, Function.update_of_ne hrs, Function.update_self]
            exact ⟨min_le_right _ _, le_max_right _ _⟩
          · simp only [p_5, p_4, p_1, l_5, l_4, l_1, u_5, u_4, u_1, Function.update_of_ne hrs, Function.update_of_ne hrt]
            exact hw' r
      have henv5 : ∀ r, L_env ≤ l_5 r ∧ u_5 r ≤ U_env := by
        intro r
        by_cases hrs : r = src
        · subst r; have h1' := henv' src
          have hlo : l_5 src = min (min (l' src) (p' src + 1)) (p' src + 1 + 1) := by
            dsimp [l_5, l_4, l_1, p_4, p_1]; rw [Function.update_self, Function.update_of_ne hne, Function.update_self, Function.update_of_ne hne, Function.update_self]
          have hhi : u_5 src = max (max (u' src) (p' src + 1)) (p' src + 1 + 1) := by
            dsimp [u_5, u_4, u_1, p_4, p_1]; rw [Function.update_self, Function.update_of_ne hne, Function.update_self, Function.update_of_ne hne, Function.update_self]
          rw [hlo, hhi, hpR1']
          exact ⟨le_min (le_min h1'.1 (by have := (hw' src).1; omega)) (by have := (hw' src).1; omega),
                 max_le (max_le h1'.2 (by omega)) (by omega)⟩
        · by_cases hrt : r = tSt
          · subst r; have h1' := henv' tSt
            simp only [l_5, l_4, l_1, u_5, u_4, u_1, p_4, p_1, Function.update_of_ne hrs, Function.update_self, hpSt']
            exact ⟨le_min h1'.1 (by have := (hw' tSt).1; omega), max_le h1'.2 (by omega)⟩
          · simp only [l_5, l_4, l_1, u_5, u_4, u_1, Function.update_of_ne hrs, Function.update_of_ne hrt]
            exact henv' r
      have ht5R1 : ∀ z : ℤ, absCell (t_5 src) ((1 + 2 * (k + 1) : ℕ) : ℤ) z = absCell ts0 1 z := by
        intro z
        have heq : t_5 src = (t_1 src).move .right := by
          dsimp [t_5, t_4, t_3]; rw [Function.update_self, Function.update_of_ne hne, Function.update_of_ne hne]
        rw [heq, show ((1 + 2 * (k + 1) : ℕ) : ℤ) = ((1 + 2 * k + 1 : ℕ) : ℤ) + 1 by omega,
          absCell_move_right, ht1S z]
      have ht5St : IsWordAt (t_5 tSt) ((k + 1 : ℕ) : ℤ) (st'.take (k + 1)) := by
        intro z
        have heq : t_5 tSt = ((t' tSt).write (some b)).move .right := by
          dsimp [t_5, t_4, t_3, t_1]
          rw [Function.update_of_ne hne.symm, Function.update_self, Function.update_self, Function.update_of_ne hne.symm]
        rw [heq, show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by omega, absCell_move_right, absCell_write, htSt' z]
        have hlen0 : (st'.take k).length = k := List.length_take_of_le (by omega)
        have hlen1 : (st'.take (k + 1)).length = k + 1 := List.length_take_of_le (Nat.succ_le_of_lt hlt)
        by_cases hz : z = (k : ℤ)
        · subst z; rw [if_pos rfl, dif_pos ⟨by omega, by omega⟩]
          have hg : (st'.take (k + 1))[k] = b := by simp [List.getElem_take, b]
          simpa using hg
        · rw [if_neg hz]
          by_cases h0 : 0 ≤ z ∧ z.toNat < k
          · rw [dif_pos ⟨h0.1, by omega⟩, dif_pos ⟨h0.1, by omega⟩]
            simp [List.getElem_take]
          · rw [dif_neg (by omega), dif_neg (by omega)]
      obtain ⟨t1, p1, l1, u1, n1, htail, hn1, hout1, ht1R1, hp1R1, ht1St, hp1St, hw1, henv1⟩ :=
        ih (k + 1) hlt (by omega) t_5 p_5 l_5 u_5 hw5 henv5 hp5R1 hp5St ht5R1 ht5St
      refine ⟨t1, p1, l1, u1, 6 + n1, trace_prepend6 hs0 hs1 hs2 hs3 hs4 hs5 htail, by omega,
        ?_, ht1R1, hp1R1, ht1St, hp1St, hw1, henv1⟩
      intro r hr1 hr2
      have ho := hout1 r hr1 hr2
      simp only [t_5, t_4, t_3, t_1, p_5, p_4, p_1, l_5, l_4, l_1, u_5, u_4, u_1,
        Function.update_of_ne hr1, Function.update_of_ne hr2] at ho
      exact ho
  obtain ⟨t1, p1, l1, u1, n, htr, hn, hout, ht1R1, hp1R1, ht1St, hp1St, hw1, henv1⟩ :=
    ind st'.length 0 (Nat.zero_le _) (Nat.sub_zero _) t p l u hw henv
      (by simpa using hpR1) (by simpa using hpSt) (fun _ => rfl) (by simpa [isWordAt_zero_iff] using htSt)
  exact ⟨t1, p1, l1, u1, n, htr, hn, hout, fun z => (ht1R1 z).trans (htR1 z), hp1R1, ht1St, hp1St, hw1, henv1⟩

private theorem emb1_update {r1 r2 : ℕ} {α : Type*} (base : LTape r1 r2 → α) (f : Fin r1 → α)
    (j : Fin r1) (v : α) :
    Function.update (fun r => match r with | .inr (.inl i) => f i | r => base r) (tR1 j) v =
      (fun r => match r with | .inr (.inl i) => Function.update f j v i | r => base r) := by
  funext r
  rcases r with i | (i | i)
  · simp [Function.update_of_ne]
  · by_cases hi : i = j
    · subst hi; simp
    · simp [Function.update_of_ne, hi]
  · simp [Function.update_of_ne]

private theorem emb2_update {r1 r2 : ℕ} {α : Type*} (base : LTape r1 r2 → α) (f : Fin r2 → α)
    (j : Fin r2) (v : α) :
    Function.update (fun r => match r with | .inr (.inr i) => f i | r => base r) (tR2 j) v =
      (fun r => match r with | .inr (.inr i) => Function.update f j v i | r => base r) := by
  funext r
  rcases r with i | (i | i)
  · simp [Function.update_of_ne]
  · simp [Function.update_of_ne]
  · by_cases hi : i = j
    · subst hi; simp
    · simp [Function.update_of_ne, hi]

private theorem lPhase_embed_R1
    (w out1 : List Bool) (n B : ℕ) (final : LocatedCfg R₁)
    (ht : Computation.Trace (locatedStep R₁) n (locatedInit R₁ w) final)
    (hh : ∃ b : Bool, final.config.state = .inl b)
    (ho : final.config.tapes R₁.inputTape = Turing.Tape.mk₁ (out1.map some))
    (hother : ∀ j : Fin R₁.tapeCount, j ≠ R₁.inputTape → final.config.tapes j = Turing.Tape.mk₁ [])
    (hpos : ∀ j : Fin R₁.tapeCount, final.position j = 0)
    (hbound : ∀ j : Fin R₁.tapeCount, -(B : ℤ) ≤ final.lower j ∧ final.upper j ≤ (B : ℤ))
    (t0 : LCfg R₁.tapeCount R₂.tapeCount) (p0 l0 u0 : LPos R₁.tapeCount R₂.tapeCount)
    (L_env U_env : ℤ)
    (hLB : L_env ≤ -(B : ℤ)) (hBU : (B : ℤ) ≤ U_env)
    (hw0 : ∀ r, l0 r ≤ p0 r ∧ p0 r ≤ u0 r) (henv0 : ∀ r, L_env ≤ l0 r ∧ u0 r ≤ U_env)
    (ht0_in : t0 (tR1 R₁.inputTape) = Turing.Tape.mk₁ (w.map some))
    (ht0_other : ∀ j : Fin R₁.tapeCount, j ≠ R₁.inputTape → t0 (tR1 j) = Turing.Tape.mk₁ [])
    (hp0 : ∀ j : Fin R₁.tapeCount, p0 (tR1 j) = 0) :
    ∃ t1 p1 l1 u1,
      Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (.inr (.inl R₁.start))) t0 p0 l0 u0)
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qBranchOut) t1 p1 l1 u1) ∧
      (∀ r, (∀ j, r ≠ tR1 j) → t1 r = t0 r ∧ p1 r = p0 r ∧ l1 r = l0 r ∧ u1 r = u0 r) ∧
      t1 (tR1 R₁.inputTape) = Turing.Tape.mk₁ (out1.map some) ∧
      (∀ j : Fin R₁.tapeCount, j ≠ R₁.inputTape → t1 (tR1 j) = Turing.Tape.mk₁ []) ∧
      (∀ j : Fin R₁.tapeCount, p1 (tR1 j) = 0) ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) := by
  let embT (c : LocatedCfg R₁) : LCfg R₁.tapeCount R₂.tapeCount :=
    fun r => match r with | .inr (.inl j) => c.config.tapes j | r => t0 r
  let embP (c : LocatedCfg R₁) : LPos R₁.tapeCount R₂.tapeCount :=
    fun r => match r with | .inr (.inl j) => c.position j | r => p0 r
  have gen : ∀ (m : ℕ) (c : LocatedCfg R₁) (q : Fin R₁.stateCount)
      (hcst : c.config.state = .inr q) (hcwf : MachineComposition.LocatedWellFormed c)
      (hcm : Computation.Trace (locatedStep R₁) m c final)
      (l' u' : LPos R₁.tapeCount R₂.tapeCount)
      (hw' : ∀ r, l' r ≤ embP c r ∧ embP c r ≤ u' r)
      (henv' : ∀ r, L_env ≤ l' r ∧ u' r ≤ U_env)
      (hlux : ∀ r, (∀ j, r ≠ tR1 j) → l' r = l0 r ∧ u' r = u0 r),
      ∃ l1 u1,
        Computation.Trace (locatedStep (loopMachine R₁ R₂)) m
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (.inr (.inl q))) (embT c) (embP c) l' u')
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qBranchOut) (embT final) (embP final) l1 u1) ∧
        (∀ r, l1 r ≤ embP final r ∧ embP final r ≤ u1 r) ∧
        (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) ∧
        (∀ r, (∀ j, r ≠ tR1 j) → l1 r = l0 r ∧ u1 r = u0 r) := by
    intro m
    induction m with
    | zero =>
      intro c q hcst _ hcm _ _ _ _ _
      cases hcm
      rcases hh with ⟨b, hb⟩
      rw [hcst] at hb; cases hb
    | succ m ih =>
      intro c q hcst hcwf hcm l' u' hw' henv' hlux
      cases hcm with
      | cons hstep htail =>
        rename_i c'
        have hc'wf := MachineComposition.locatedWellFormed_step hcwf hstep
        have hfb := locatedTrace_bounds_mono htail
        have hop : loopOps R₁ R₂ (.inr (.inl q)) =
            .raw (tR1 (R₁.scan q)) (fun sym =>
              match R₁.transition q sym with
              | .inl _ => .inr (qBranchOut, .write sym)
              | .inr (q1', stmt) => .inr (.inr (.inl q1'), stmt)) := rfl
        obtain ⟨cfg', hcfgStep, hmon⟩ : ∃ cfg', R₁.step c.config = some cfg' ∧ c.monitor cfg' = c' := by
          cases hs : R₁.step c.config with
          | none => simp [locatedStep, hs] at hstep
          | some d' => exact ⟨d', rfl, by simpa [locatedStep, hs] using hstep⟩
        have hc'_cfg : c'.config = cfg' := by
          rw [← hmon]; simp only [LocatedCfg.monitor, hcst, Sum.elim_inr]
          cases R₁.transition q (c.config.tapes (R₁.scan q)).head <;> rfl
        rw [← hc'_cfg] at hcfgStep hmon
        simp only [PrimitiveMachine.step, hcst] at hcfgStep
        cases htr : R₁.transition q (c.config.tapes (R₁.scan q)).head with
        | inl b =>
          simp only [htr, Option.some.injEq] at hcfgStep
          have hfin_m : c' = final ∧ m = 0 := by
            cases htail with
            | refl => exact ⟨rfl, rfl⟩
            | cons hst2 _ =>
              exfalso
              have hc'st : c'.config.state = .inl b := by rw [← hcfgStep]
              simp [locatedStep, PrimitiveMachine.step, hc'st] at hst2
          rcases hfin_m with ⟨rfl, rfl⟩
          have hmon_eq : c' = c.monitor ⟨.inl b, c.config.tapes⟩ := by
            rw [hcfgStep]; exact hmon.symm
          have htapes : c'.config.tapes = c.config.tapes := by
            rw [← hcfgStep]
          have hpos_eq : c'.position = c.position := by
            have hm : c.monitor ⟨.inl b, c.config.tapes⟩ =
                { c with config := ⟨.inl b, c.config.tapes⟩ } := by
              simp [LocatedCfg.monitor, hcst, htr]
            rw [hmon_eq, hm]
          have hembT : embT c' = embT c := by
            funext r; rcases r with i | (i | i) <;> simp [embT, htapes]
          have hembP : embP c' = embP c := by
            funext r; rcases r with i | (i | i) <;> simp [embP, hpos_eq]
          have htr_m : (fun sym => (match R₁.transition q sym with
              | .inl _ => .inr (qBranchOut, .write sym)
              | .inr (q1', stmt) => .inr (.inr (.inl q1'), stmt) :
                Bool ⊕ (LQ R₁.stateCount R₂.stateCount × Turing.TM0.Stmt (Option Bool))))
              ((embT c) (tR1 (R₁.scan q))).head = .inr (qBranchOut, .write ((embT c) (tR1 (R₁.scan q))).head) := by
            simp [embT, htr]
          have hs0 := lStep_raw_write R₁ R₂ hop (embT c) (embP c) l' u' htr_m (hw' (tR1 (R₁.scan q)))
          rw [Turing.Tape.write_self, Function.update_eq_self] at hs0
          have hs0' : locatedStep (loopMachine R₁ R₂)
              (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (.inr (.inl q))) (embT c) (embP c) l' u') =
              some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qBranchOut) (embT c') (embP c') l' u') := by
            rw [hembT, hembP]; exact hs0
          refine ⟨l', u', .cons hs0' (.refl _), ?_, henv', hlux⟩
          simpa [hembP] using hw'
        | inr qa =>
          rcases qa with ⟨q', stmt⟩
          cases stmt with
          | write sym =>
            simp only [htr, Option.some.injEq] at hcfgStep
            have hpos' : c'.position = c.position := by
              rw [← hmon]; simp [LocatedCfg.monitor, hcst, htr, headDisplacement]
            have htapes' : c'.config.tapes = Function.update c.config.tapes (R₁.scan q)
                ((c.config.tapes (R₁.scan q)).write sym) := by
              rw [← hcfgStep]
            have hembT' : embT c' = Function.update (embT c) (tR1 (R₁.scan q))
                (((embT c) (tR1 (R₁.scan q))).write sym) := by
              funext r; rcases r with i | (i | i)
              · simp [embT, Function.update_of_ne]
              · by_cases hi : i = R₁.scan q
                · subst hi; simp [embT, htapes']
                · simp [embT, htapes', Function.update_of_ne hi]
              · simp [embT, Function.update_of_ne]
            have hembP' : embP c' = embP c := by
              funext r; rcases r with i | (i | i) <;> simp [embP, hpos']
            have htr_m : (fun s => (match R₁.transition q s with
                | .inl _ => .inr (qBranchOut, .write s)
                | .inr (q1', st) => .inr (.inr (.inl q1'), st) :
                  Bool ⊕ (LQ R₁.stateCount R₂.stateCount × Turing.TM0.Stmt (Option Bool))))
                ((embT c) (tR1 (R₁.scan q))).head = .inr (.inr (.inl q'), .write sym) := by
              simp [embT, htr]
            have hs0 := lStep_raw_write R₁ R₂ hop (embT c) (embP c) l' u' htr_m (hw' (tR1 (R₁.scan q)))
            have hs0' : locatedStep (loopMachine R₁ R₂)
                (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (.inr (.inl q))) (embT c) (embP c) l' u') =
                some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (.inr (.inl q'))) (embT c') (embP c') l' u') := by
              rw [hembP']; simpa [← hembT'] using hs0
            obtain ⟨l1, u1, hrest, hw1, henv1, hlux1⟩ :=
              ih c' q' (by rw [← hcfgStep]) hc'wf htail l' u' (by simpa [hembP'] using hw') henv' hlux
            exact ⟨l1, u1, .cons hs0' hrest, hw1, henv1, hlux1⟩
          | move dir =>
            simp only [htr, Option.some.injEq] at hcfgStep
            have hmon_dir : c' =
                { config := c'.config
                  position := Function.update c.position (R₁.scan q) (c.position (R₁.scan q) + headDisplacement (.move dir))
                  lower := Function.update c.lower (R₁.scan q) (min (c.lower (R₁.scan q)) (c.position (R₁.scan q) + headDisplacement (.move dir)))
                  upper := Function.update c.upper (R₁.scan q) (max (c.upper (R₁.scan q)) (c.position (R₁.scan q) + headDisplacement (.move dir))) } := by
              rw [← hmon]; unfold LocatedCfg.monitor; simp [hcst, htr]
            have htapes' : c'.config.tapes = Function.update c.config.tapes (R₁.scan q)
                ((c.config.tapes (R₁.scan q)).move dir) := by
              rw [← hcfgStep]
            have hembT' : embT c' = Function.update (embT c) (tR1 (R₁.scan q))
                (((embT c) (tR1 (R₁.scan q))).move dir) := by
              funext r; rcases r with i | (i | i)
              · simp [embT, Function.update_of_ne]
              · by_cases hi : i = R₁.scan q
                · subst hi; simp [embT, htapes']
                · simp [embT, htapes', Function.update_of_ne hi]
              · simp [embT, Function.update_of_ne]
            have hpos_upd : c'.position = Function.update c.position (R₁.scan q)
                (c.position (R₁.scan q) + headDisplacement (.move dir)) := by
              rw [hmon_dir]
            have hembP' : embP c' = Function.update (embP c) (tR1 (R₁.scan q))
                (embP c (tR1 (R₁.scan q)) + headDisplacement (.move dir)) := by
              funext r; rcases r with i | (i | i)
              · simp [embP, Function.update_of_ne]
              · by_cases hi : i = R₁.scan q
                · subst hi; simp [embP, hpos_upd]
                · simp [embP, hpos_upd, Function.update_of_ne hi]
              · simp [embP, Function.update_of_ne]
            have htr_m : (fun s => (match R₁.transition q s with
                | .inl _ => .inr (qBranchOut, .write s)
                | .inr (q1', st) => .inr (.inr (.inl q1'), st) :
                  Bool ⊕ (LQ R₁.stateCount R₂.stateCount × Turing.TM0.Stmt (Option Bool))))
                ((embT c) (tR1 (R₁.scan q))).head = .inr (.inr (.inl q'), .move dir) := by
              simp [embT, htr]
            have hs0 := lStep_raw_move R₁ R₂ hop (embT c) (embP c) l' u' htr_m
            let pos' := embP c (tR1 (R₁.scan q)) + headDisplacement (.move dir)
            let l'' := Function.update l' (tR1 (R₁.scan q)) (min (l' (tR1 (R₁.scan q))) pos')
            let u'' := Function.update u' (tR1 (R₁.scan q)) (max (u' (tR1 (R₁.scan q))) pos')
            have hpos_b : L_env ≤ pos' ∧ pos' ≤ U_env := by
              have hbw := hbound (R₁.scan q)
              have hfm := hfb (R₁.scan q)
              have hwf' := hc'wf (R₁.scan q)
              have hp_eq : pos' = c'.position (R₁.scan q) := by simp [pos', embP, hpos_upd]
              rw [hp_eq]
              exact ⟨by omega, by omega⟩
            have hw'' : ∀ r, l'' r ≤ embP c' r ∧ embP c' r ≤ u'' r := by
              intro r; rw [hembP']
              by_cases hr : r = tR1 (R₁.scan q)
              · subst r; simp only [l'', u'', Function.update_self, pos']; exact ⟨min_le_right _ _, le_max_right _ _⟩
              · simp only [l'', u'', Function.update_of_ne hr]; exact hw' r
            have henv'' : ∀ r, L_env ≤ l'' r ∧ u'' r ≤ U_env := by
              intro r
              by_cases hr : r = tR1 (R₁.scan q)
              · subst r; have h1' := henv' (tR1 (R₁.scan q))
                simp only [l'', u'', Function.update_self]
                exact ⟨le_min h1'.1 hpos_b.1, max_le h1'.2 hpos_b.2⟩
              · simp only [l'', u'', Function.update_of_ne hr]; exact henv' r
            have hlux'' : ∀ r, (∀ j, r ≠ tR1 j) → l'' r = l0 r ∧ u'' r = u0 r := by
              intro r hnr
              have hne := hnr (R₁.scan q)
              simp only [l'', u'', Function.update_of_ne hne]
              exact hlux r hnr
            dsimp only at hs0
            rw [← hembT', ← hembP'] at hs0
            obtain ⟨l1, u1, hrest, hw1, henv1, hlux1⟩ :=
              ih c' q' (by rw [← hcfgStep]) hc'wf htail l'' u'' hw'' henv'' hlux''
            exact ⟨l1, u1, .cons hs0 hrest, hw1, henv1, hlux1⟩
  have hembT_init : embT (locatedInit R₁ w) = t0 := by
    funext r
    rcases r with i | (j | j)
    · rfl
    · dsimp [embT, locatedInit, PrimitiveMachine.init]
      by_cases hj : j = R₁.inputTape
      · subst hj; simp [ht0_in]
      · simp [hj, ht0_other j hj]
    · rfl
  have hembP_init : embP (locatedInit R₁ w) = p0 := by
    funext r
    rcases r with i | (j | j)
    · rfl
    · simp [embP, locatedInit, hp0 j]
    · rfl
  have hw_init : ∀ r, l0 r ≤ embP (locatedInit R₁ w) r ∧ embP (locatedInit R₁ w) r ≤ u0 r := by
    simpa [hembP_init] using hw0
  obtain ⟨l1, u1, htr, hw1, henv1, hlux1⟩ :=
    gen n (locatedInit R₁ w) R₁.start rfl (MachineComposition.locatedWellFormed_init R₁ w) ht
      l0 u0 hw_init henv0 (fun r _ => ⟨rfl, rfl⟩)
  rw [hembT_init, hembP_init] at htr
  refine ⟨embT final, embP final, l1, u1, htr, ?_, ?_, ?_, ?_, hw1, henv1⟩
  · intro r hnr
    have hlu := hlux1 r hnr
    rcases r with i | (j | j)
    · exact ⟨rfl, rfl, hlu.1, hlu.2⟩
    · exact absurd rfl (hnr j)
    · exact ⟨rfl, rfl, hlu.1, hlu.2⟩
  · simpa [embT] using ho
  · intro j hj; simpa [embT] using hother j hj
  · intro j; simpa [embP] using hpos j

private theorem lPhase_embed_R2
    (w out2 : List Bool) (n B : ℕ) (final : LocatedCfg R₂)
    (ht : Computation.Trace (locatedStep R₂) n (locatedInit R₂ w) final)
    (hh : ∃ b : Bool, final.config.state = .inl b)
    (ho : final.config.tapes R₂.inputTape = Turing.Tape.mk₁ (out2.map some))
    (hother : ∀ j : Fin R₂.tapeCount, j ≠ R₂.inputTape → final.config.tapes j = Turing.Tape.mk₁ [])
    (hpos : ∀ j : Fin R₂.tapeCount, final.position j = 0)
    (hbound : ∀ j : Fin R₂.tapeCount, -(B : ℤ) ≤ final.lower j ∧ final.upper j ≤ (B : ℤ))
    (t0 : LCfg R₁.tapeCount R₂.tapeCount) (p0 l0 u0 : LPos R₁.tapeCount R₂.tapeCount)
    (L_env U_env : ℤ)
    (hLB : L_env ≤ -(B : ℤ)) (hBU : (B : ℤ) ≤ U_env)
    (hw0 : ∀ r, l0 r ≤ p0 r ∧ p0 r ≤ u0 r) (henv0 : ∀ r, L_env ≤ l0 r ∧ u0 r ≤ U_env)
    (ht0_in : t0 (tR2 R₂.inputTape) = Turing.Tape.mk₁ (w.map some))
    (ht0_other : ∀ j : Fin R₂.tapeCount, j ≠ R₂.inputTape → t0 (tR2 j) = Turing.Tape.mk₁ [])
    (hp0 : ∀ j : Fin R₂.tapeCount, p0 (tR2 j) = 0) :
    ∃ t1 p1 l1 u1,
      Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (.inr (.inr R₂.start))) t0 p0 l0 u0)
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qRetAnsCheck) t1 p1 l1 u1) ∧
      (∀ r, (∀ j, r ≠ tR2 j) → t1 r = t0 r ∧ p1 r = p0 r ∧ l1 r = l0 r ∧ u1 r = u0 r) ∧
      t1 (tR2 R₂.inputTape) = Turing.Tape.mk₁ (out2.map some) ∧
      (∀ j : Fin R₂.tapeCount, j ≠ R₂.inputTape → t1 (tR2 j) = Turing.Tape.mk₁ []) ∧
      (∀ j : Fin R₂.tapeCount, p1 (tR2 j) = 0) ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧ (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) := by
  let embT (c : LocatedCfg R₂) : LCfg R₁.tapeCount R₂.tapeCount :=
    fun r => match r with | .inr (.inr j) => c.config.tapes j | r => t0 r
  let embP (c : LocatedCfg R₂) : LPos R₁.tapeCount R₂.tapeCount :=
    fun r => match r with | .inr (.inr j) => c.position j | r => p0 r
  have gen : ∀ (m : ℕ) (c : LocatedCfg R₂) (q : Fin R₂.stateCount)
      (hcst : c.config.state = .inr q) (hcwf : MachineComposition.LocatedWellFormed c)
      (hcm : Computation.Trace (locatedStep R₂) m c final)
      (l' u' : LPos R₁.tapeCount R₂.tapeCount)
      (hw' : ∀ r, l' r ≤ embP c r ∧ embP c r ≤ u' r)
      (henv' : ∀ r, L_env ≤ l' r ∧ u' r ≤ U_env)
      (hlux : ∀ r, (∀ j, r ≠ tR2 j) → l' r = l0 r ∧ u' r = u0 r),
      ∃ l1 u1,
        Computation.Trace (locatedStep (loopMachine R₁ R₂)) m
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (.inr (.inr q))) (embT c) (embP c) l' u')
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qRetAnsCheck) (embT final) (embP final) l1 u1) ∧
        (∀ r, l1 r ≤ embP final r ∧ embP final r ≤ u1 r) ∧
        (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) ∧
        (∀ r, (∀ j, r ≠ tR2 j) → l1 r = l0 r ∧ u1 r = u0 r) := by
    intro m
    induction m with
    | zero =>
      intro c q hcst _ hcm _ _ _ _ _
      cases hcm
      rcases hh with ⟨b, hb⟩
      rw [hcst] at hb; cases hb
    | succ m ih =>
      intro c q hcst hcwf hcm l' u' hw' henv' hlux
      cases hcm with
      | cons hstep htail =>
        rename_i c'
        have hc'wf := MachineComposition.locatedWellFormed_step hcwf hstep
        have hfb := locatedTrace_bounds_mono htail
        have hop : loopOps R₁ R₂ (.inr (.inr q)) =
            .raw (tR2 (R₂.scan q)) (fun sym =>
              match R₂.transition q sym with
              | .inl _ => .inr (qRetAnsCheck, .write sym)
              | .inr (q2', stmt) => .inr (.inr (.inr q2'), stmt)) := rfl
        obtain ⟨cfg', hcfgStep, hmon⟩ : ∃ cfg', R₂.step c.config = some cfg' ∧ c.monitor cfg' = c' := by
          cases hs : R₂.step c.config with
          | none => simp [locatedStep, hs] at hstep
          | some d' => exact ⟨d', rfl, by simpa [locatedStep, hs] using hstep⟩
        have hc'_cfg : c'.config = cfg' := by
          rw [← hmon]; simp only [LocatedCfg.monitor, hcst, Sum.elim_inr]
          cases R₂.transition q (c.config.tapes (R₂.scan q)).head <;> rfl
        rw [← hc'_cfg] at hcfgStep hmon
        simp only [PrimitiveMachine.step, hcst] at hcfgStep
        cases htr : R₂.transition q (c.config.tapes (R₂.scan q)).head with
        | inl b =>
          simp only [htr, Option.some.injEq] at hcfgStep
          have hfin_m : c' = final ∧ m = 0 := by
            cases htail with
            | refl => exact ⟨rfl, rfl⟩
            | cons hst2 _ =>
              exfalso
              have hc'st : c'.config.state = .inl b := by rw [← hcfgStep]
              simp [locatedStep, PrimitiveMachine.step, hc'st] at hst2
          rcases hfin_m with ⟨rfl, rfl⟩
          have hmon_eq : c' = c.monitor ⟨.inl b, c.config.tapes⟩ := by
            rw [hcfgStep]; exact hmon.symm
          have htapes : c'.config.tapes = c.config.tapes := by
            rw [← hcfgStep]
          have hpos_eq : c'.position = c.position := by
            have hm : c.monitor ⟨.inl b, c.config.tapes⟩ =
                { c with config := ⟨.inl b, c.config.tapes⟩ } := by
              simp [LocatedCfg.monitor, hcst, htr]
            rw [hmon_eq, hm]
          have hembT : embT c' = embT c := by
            funext r; rcases r with i | (i | i) <;> simp [embT, htapes]
          have hembP : embP c' = embP c := by
            funext r; rcases r with i | (i | i) <;> simp [embP, hpos_eq]
          have htr_m : (fun sym => (match R₂.transition q sym with
              | .inl _ => .inr (qRetAnsCheck, .write sym)
              | .inr (q2', stmt) => .inr (.inr (.inr q2'), stmt) :
                Bool ⊕ (LQ R₁.stateCount R₂.stateCount × Turing.TM0.Stmt (Option Bool))))
              ((embT c) (tR2 (R₂.scan q))).head = .inr (qRetAnsCheck, .write ((embT c) (tR2 (R₂.scan q))).head) := by
            simp [embT, htr]
          have hs0 := lStep_raw_write R₁ R₂ hop (embT c) (embP c) l' u' htr_m (hw' (tR2 (R₂.scan q)))
          rw [Turing.Tape.write_self, Function.update_eq_self] at hs0
          have hs0' : locatedStep (loopMachine R₁ R₂)
              (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (.inr (.inr q))) (embT c) (embP c) l' u') =
              some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qRetAnsCheck) (embT c') (embP c') l' u') := by
            rw [hembT, hembP]; exact hs0
          refine ⟨l', u', .cons hs0' (.refl _), ?_, henv', hlux⟩
          simpa [hembP] using hw'
        | inr qa =>
          rcases qa with ⟨q', stmt⟩
          cases stmt with
          | write sym =>
            simp only [htr, Option.some.injEq] at hcfgStep
            have hpos' : c'.position = c.position := by
              rw [← hmon]; simp [LocatedCfg.monitor, hcst, htr, headDisplacement]
            have htapes' : c'.config.tapes = Function.update c.config.tapes (R₂.scan q)
                ((c.config.tapes (R₂.scan q)).write sym) := by
              rw [← hcfgStep]
            have hembT' : embT c' = Function.update (embT c) (tR2 (R₂.scan q))
                (((embT c) (tR2 (R₂.scan q))).write sym) := by
              funext r; rcases r with i | (i | i)
              · simp [embT, Function.update_of_ne]
              · simp [embT, Function.update_of_ne]
              · by_cases hi : i = R₂.scan q
                · subst hi; simp [embT, htapes']
                · simp [embT, htapes', Function.update_of_ne hi]
            have hembP' : embP c' = embP c := by
              funext r; rcases r with i | (i | i) <;> simp [embP, hpos']
            have htr_m : (fun s => (match R₂.transition q s with
                | .inl _ => .inr (qRetAnsCheck, .write s)
                | .inr (q2', st) => .inr (.inr (.inr q2'), st) :
                  Bool ⊕ (LQ R₁.stateCount R₂.stateCount × Turing.TM0.Stmt (Option Bool))))
                ((embT c) (tR2 (R₂.scan q))).head = .inr (.inr (.inr q'), .write sym) := by
              simp [embT, htr]
            have hs0 := lStep_raw_write R₁ R₂ hop (embT c) (embP c) l' u' htr_m (hw' (tR2 (R₂.scan q)))
            have hs0' : locatedStep (loopMachine R₁ R₂)
                (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (.inr (.inr q))) (embT c) (embP c) l' u') =
                some (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr (.inr (.inr q'))) (embT c') (embP c') l' u') := by
              rw [hembP']; simpa [← hembT'] using hs0
            obtain ⟨l1, u1, hrest, hw1, henv1, hlux1⟩ :=
              ih c' q' (by rw [← hcfgStep]) hc'wf htail l' u' (by simpa [hembP'] using hw') henv' hlux
            exact ⟨l1, u1, .cons hs0' hrest, hw1, henv1, hlux1⟩
          | move dir =>
            simp only [htr, Option.some.injEq] at hcfgStep
            have hmon_dir : c' =
                { config := c'.config
                  position := Function.update c.position (R₂.scan q) (c.position (R₂.scan q) + headDisplacement (.move dir))
                  lower := Function.update c.lower (R₂.scan q) (min (c.lower (R₂.scan q)) (c.position (R₂.scan q) + headDisplacement (.move dir)))
                  upper := Function.update c.upper (R₂.scan q) (max (c.upper (R₂.scan q)) (c.position (R₂.scan q) + headDisplacement (.move dir))) } := by
              rw [← hmon]; unfold LocatedCfg.monitor; simp [hcst, htr]
            have htapes' : c'.config.tapes = Function.update c.config.tapes (R₂.scan q)
                ((c.config.tapes (R₂.scan q)).move dir) := by
              rw [← hcfgStep]
            have hembT' : embT c' = Function.update (embT c) (tR2 (R₂.scan q))
                (((embT c) (tR2 (R₂.scan q))).move dir) := by
              funext r; rcases r with i | (i | i)
              · simp [embT, Function.update_of_ne]
              · simp [embT, Function.update_of_ne]
              · by_cases hi : i = R₂.scan q
                · subst hi; simp [embT, htapes']
                · simp [embT, htapes', Function.update_of_ne hi]
            have hpos_upd : c'.position = Function.update c.position (R₂.scan q)
                (c.position (R₂.scan q) + headDisplacement (.move dir)) := by
              rw [hmon_dir]
            have hembP' : embP c' = Function.update (embP c) (tR2 (R₂.scan q))
                (embP c (tR2 (R₂.scan q)) + headDisplacement (.move dir)) := by
              funext r; rcases r with i | (i | i)
              · simp [embP, Function.update_of_ne]
              · simp [embP, Function.update_of_ne]
              · by_cases hi : i = R₂.scan q
                · subst hi; simp [embP, hpos_upd]
                · simp [embP, hpos_upd, Function.update_of_ne hi]
            have htr_m : (fun s => (match R₂.transition q s with
                | .inl _ => .inr (qRetAnsCheck, .write s)
                | .inr (q2', st) => .inr (.inr (.inr q2'), st) :
                  Bool ⊕ (LQ R₁.stateCount R₂.stateCount × Turing.TM0.Stmt (Option Bool))))
                ((embT c) (tR2 (R₂.scan q))).head = .inr (.inr (.inr q'), .move dir) := by
              simp [embT, htr]
            have hs0 := lStep_raw_move R₁ R₂ hop (embT c) (embP c) l' u' htr_m
            let pos' := embP c (tR2 (R₂.scan q)) + headDisplacement (.move dir)
            let l'' := Function.update l' (tR2 (R₂.scan q)) (min (l' (tR2 (R₂.scan q))) pos')
            let u'' := Function.update u' (tR2 (R₂.scan q)) (max (u' (tR2 (R₂.scan q))) pos')
            have hpos_b : L_env ≤ pos' ∧ pos' ≤ U_env := by
              have hbw := hbound (R₂.scan q)
              have hfm := hfb (R₂.scan q)
              have hwf' := hc'wf (R₂.scan q)
              have hp_eq : pos' = c'.position (R₂.scan q) := by simp [pos', embP, hpos_upd]
              rw [hp_eq]
              exact ⟨by omega, by omega⟩
            have hw'' : ∀ r, l'' r ≤ embP c' r ∧ embP c' r ≤ u'' r := by
              intro r; rw [hembP']
              by_cases hr : r = tR2 (R₂.scan q)
              · subst r; simp only [l'', u'', Function.update_self, pos']; exact ⟨min_le_right _ _, le_max_right _ _⟩
              · simp only [l'', u'', Function.update_of_ne hr]; exact hw' r
            have henv'' : ∀ r, L_env ≤ l'' r ∧ u'' r ≤ U_env := by
              intro r
              by_cases hr : r = tR2 (R₂.scan q)
              · subst r; have h1' := henv' (tR2 (R₂.scan q))
                simp only [l'', u'', Function.update_self]
                exact ⟨le_min h1'.1 hpos_b.1, max_le h1'.2 hpos_b.2⟩
              · simp only [l'', u'', Function.update_of_ne hr]; exact henv' r
            have hlux'' : ∀ r, (∀ j, r ≠ tR2 j) → l'' r = l0 r ∧ u'' r = u0 r := by
              intro r hnr
              have hne := hnr (R₂.scan q)
              simp only [l'', u'', Function.update_of_ne hne]
              exact hlux r hnr
            dsimp only at hs0
            rw [← hembT', ← hembP'] at hs0
            obtain ⟨l1, u1, hrest, hw1, henv1, hlux1⟩ :=
              ih c' q' (by rw [← hcfgStep]) hc'wf htail l'' u'' hw'' henv'' hlux''
            exact ⟨l1, u1, .cons hs0 hrest, hw1, henv1, hlux1⟩
  have hembT_init : embT (locatedInit R₂ w) = t0 := by
    funext r
    rcases r with i | (j | j)
    · rfl
    · rfl
    · dsimp [embT, locatedInit, PrimitiveMachine.init]
      by_cases hj : j = R₂.inputTape
      · subst hj; simp [ht0_in]
      · simp [hj, ht0_other j hj]
  have hembP_init : embP (locatedInit R₂ w) = p0 := by
    funext r
    rcases r with i | (j | j)
    · rfl
    · rfl
    · simp [embP, locatedInit, hp0 j]
  have hw_init : ∀ r, l0 r ≤ embP (locatedInit R₂ w) r ∧ embP (locatedInit R₂ w) r ≤ u0 r := by
    simpa [hembP_init] using hw0
  obtain ⟨l1, u1, htr, hw1, henv1, hlux1⟩ :=
    gen n (locatedInit R₂ w) R₂.start rfl (MachineComposition.locatedWellFormed_init R₂ w) ht
      l0 u0 hw_init henv0 (fun r _ => ⟨rfl, rfl⟩)
  rw [hembT_init, hembP_init] at htr
  refine ⟨embT final, embP final, l1, u1, htr, ?_, ?_, ?_, ?_, hw1, henv1⟩
  · intro r hnr
    have hlu := hlux1 r hnr
    rcases r with i | (j | j)
    · exact ⟨rfl, rfl, hlu.1, hlu.2⟩
    · exact ⟨rfl, rfl, hlu.1, hlu.2⟩
    · exact absurd rfl (hnr j)
  · simpa [embT] using ho
  · intro j hj; simpa [embT] using hother j hj
  · intro j; simpa [embP] using hpos j

private theorem trace_trans {α : Type*} {f : α → Option α} {m n : ℕ} {a b c : α}
    (h1 : Computation.Trace f m a b) (h2 : Computation.Trace f n b c) :
    Computation.Trace f (m + n) a c := by
  induction h1 with
  | refl => simpa using h2
  | cons hs _ ih => rw [Nat.add_right_comm]; exact .cons hs (ih h2)

private def LoopInv {r1 r2 : ℕ} (t : LCfg r1 r2) (p l u : LPos r1 r2) (L_env U_env : ℤ)
    (_in1 : Fin r1) (_in2 : Fin r2) (st ans : List Bool) : Prop :=
  t tSt = Turing.Tape.mk₁ (st.map some) ∧ p tSt = 0 ∧
  t tAns = Turing.Tape.mk₁ (ans.map some) ∧ p tAns = 0 ∧
  (∀ j, t (tR1 j) = Turing.Tape.mk₁ [] ∧ p (tR1 j) = 0) ∧
  (∀ j, t (tR2 j) = Turing.Tape.mk₁ [] ∧ p (tR2 j) = 0) ∧
  (∀ r, l r ≤ p r ∧ p r ≤ u r) ∧
  (∀ r, L_env ≤ l r ∧ u r ≤ U_env)

private theorem lPhase_run_R1
    (st ans out1 : List Bool) (n1 B1 : ℕ) (final1 : LocatedCfg R₁)
    (ht1 : Computation.Trace (locatedStep R₁) n1
      (locatedInit R₁ (st.flatMap (fun b => [true, b]) ++ [false] ++ ans)) final1)
    (hh1 : ∃ b : Bool, final1.config.state = .inl b)
    (ho1 : final1.config.tapes R₁.inputTape = Turing.Tape.mk₁ (out1.map some))
    (hother1 : ∀ j : Fin R₁.tapeCount, j ≠ R₁.inputTape → final1.config.tapes j = Turing.Tape.mk₁ [])
    (hpos1 : ∀ j : Fin R₁.tapeCount, final1.position j = 0)
    (hbound1 : ∀ j : Fin R₁.tapeCount, -(B1 : ℤ) ≤ final1.lower j ∧ final1.upper j ≤ (B1 : ℤ))
    (t : LCfg R₁.tapeCount R₂.tapeCount) (p l u : LPos R₁.tapeCount R₂.tapeCount)
    (L_env U_env : ℤ)
    (hLB : L_env ≤ -(B1 : ℤ)) (hLB1 : L_env ≤ -1) (hBU : (B1 : ℤ) ≤ U_env)
    (hMax_env : ((st.flatMap (fun b => [true, b]) ++ [false] ++ ans).length : ℤ) ≤ U_env)
    (hinv : LoopInv t p l u L_env U_env R₁.inputTape R₂.inputTape st ans) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qEncStCheck) t p l u)
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qBranchOut) t1 p1 l1 u1) ∧
      n = n1 + 13 * st.length + 9 * ans.length + 15 ∧
      t1 tSt = Turing.Tape.mk₁ [] ∧ p1 tSt = 0 ∧
      t1 tAns = Turing.Tape.mk₁ [] ∧ p1 tAns = 0 ∧
      t1 (tR1 R₁.inputTape) = Turing.Tape.mk₁ (out1.map some) ∧
      (∀ j : Fin R₁.tapeCount, j ≠ R₁.inputTape → t1 (tR1 j) = Turing.Tape.mk₁ []) ∧
      (∀ j : Fin R₁.tapeCount, p1 (tR1 j) = 0) ∧
      (∀ j : Fin R₂.tapeCount, t1 (tR2 j) = Turing.Tape.mk₁ [] ∧ p1 (tR2 j) = 0) ∧
      (∀ r, l1 r ≤ p1 r ∧ p1 r ≤ u1 r) ∧
      (∀ r, L_env ≤ l1 r ∧ u1 r ≤ U_env) := by
  rcases hinv with ⟨htSt0, hpSt0, htAns0, hpAns0, htR10, htR20, hw0, henv0⟩
  let w := st.flatMap (fun b => [true, b]) ++ [false] ++ ans
  have hw_len : w.length = 2 * st.length + 1 + ans.length := by
    dsimp [w]; rw [List.length_append, List.length_append, List.length_singleton, list_flatMap_pair_length]
  let pre := st.flatMap (fun b => [true, b]) ++ [false]
  have hpre_len : pre.length = 2 * st.length + 1 := by
    dsimp [pre]; rw [List.length_append, List.length_singleton, list_flatMap_pair_length]
  have hpre_ans : pre ++ ans = w := by simp [pre, w]
  have hpre_ans_len : pre.length + ans.length = w.length := by omega
  have hwU : (w.length : ℤ) ≤ U_env := hMax_env
  obtain ⟨t1, p1, l1, u1, n_1, tr1, hn1, hout1, ht1St, hp1St, ht1R1, hp1R1, hw1, henv1⟩ :=
    lPhase_encPairs R₁ R₂ st t p l u L_env U_env hw0 henv0 (by omega) (by omega)
      hpSt0 (htR10 R₁.inputTape).2 ((isWordAt_zero_iff _ _).mpr htSt0) (htR10 R₁.inputTape).1
  have ho_ans1 := hout1 tAns ltape_st_ne_ans.symm (ltape_ans_ne_r1 R₁.inputTape)
  have hne_ans_r1 : (tAns : LTape R₁.tapeCount R₂.tapeCount) ≠ tR1 R₁.inputTape := ltape_ans_ne_r1 R₁.inputTape
  obtain ⟨t2, p2, l2, u2, n_2, tr2, hn2, hout2, ht2Ans_abs, hp2Ans, ht2R1, hp2R1, hw2, henv2⟩ :=
    lPhase_copy R₁ R₂ qEncAnsCheck qEncAnsWT qEncAnsWF qEncAnsAdvD qEncAnsAdvS qEraseStStart
      tAns (tR1 R₁.inputTape) hne_ans_r1
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      pre ans 0 (le_refl _) t1 p1 l1 u1 L_env U_env hw1 henv1 (by omega) (by omega)
      (ho_ans1.2.1.trans hpAns0) (by rw [hpre_len]; exact hp1R1)
      (fun z hz => by
        rw [ho_ans1.1, htAns0, absCell_mk₁_zero]
        split_ifs with h1 h2
        · simp
        · exfalso; exact h2 (by omega)
        · exfalso; exact h1 (by omega)
        · rfl)
      (by rw [show (pre.length : ℤ) = ((2 * st.length + 1 : ℕ) : ℤ) by rw [hpre_len]]; exact ht1R1)
  have ht2St_eq := hout2 tSt ltape_st_ne_ans (ltape_st_ne_r1 R₁.inputTape)
  have ht2St : IsWordAt (t2 tSt) (st.length : ℤ) st := by rw [ht2St_eq.1]; exact ht1St
  have hp2St : p2 tSt = st.length := by rw [ht2St_eq.2.1, hp1St]
  obtain ⟨t3, p3, l3, u3, n_3, tr3, hn3, hout3, ht3St, hp3St, hw3, henv3⟩ :=
    lPhase_eraseLeft R₁ R₂ qEraseStStart qEraseStCheck qEraseStW qEraseStRight qEraseAnsStart tSt st.length
      (by rfl) (by rfl) (by rfl) (by rfl)
      t2 p2 l2 u2 L_env U_env hw2 henv2 hLB1 (by omega) hp2St
      (fun z => by rw [ht2St z]; split_ifs with h <;> simp <;> omega)
  have ht3Ans_eq := hout3 tAns ltape_st_ne_ans.symm
  have ht3Ans_abs : ∀ z : ℤ, absCell (t3 tAns) (ans.length : ℤ) z = none ↔ ¬ (0 ≤ z ∧ z < (ans.length : ℤ)) := by
    intro z
    rw [ht3Ans_eq.1, show (ans.length : ℤ) = 0 + (ans.length : ℤ) by omega, ht2Ans_abs z,
      ho_ans1.1, htAns0, absCell_mk₁_eq_none]; simp
  have hp3Ans : p3 tAns = ans.length := by
    rw [ht3Ans_eq.2.1]; simpa using hp2Ans
  obtain ⟨t4, p4, l4, u4, n_4, tr4, hn4, hout4, ht4Ans, hp4Ans, hw4, henv4⟩ :=
    lPhase_eraseLeft R₁ R₂ qEraseAnsStart qEraseAnsCheck qEraseAnsW qEraseAnsRight qRewR1Start tAns ans.length
      (by rfl) (by rfl) (by rfl) (by rfl)
      t3 p3 l3 u3 L_env U_env hw3 henv3 hLB1 (by omega) hp3Ans ht3Ans_abs
  have hw4_eq : ∀ z : ℤ, absCell (t4 (tR1 R₁.inputTape)) (w.length : ℤ) z =
      if h : 0 ≤ z ∧ z.toNat < w.length then some w[z.toNat] else none := by
    have h4r1 := hout4 (tR1 R₁.inputTape) (ltape_ans_ne_r1 R₁.inputTape).symm
    have h3r1 := hout3 (tR1 R₁.inputTape) (ltape_st_ne_r1 R₁.inputTape).symm
    intro z
    rw [h4r1.1, h3r1.1]
    have h := ht2R1 z
    simpa [hpre_ans, hpre_ans_len] using h
  have hp4R1 : p4 (tR1 R₁.inputTape) = w.length := by
    have h4r1 := hout4 (tR1 R₁.inputTape) (ltape_ans_ne_r1 R₁.inputTape).symm
    have h3r1 := hout3 (tR1 R₁.inputTape) (ltape_st_ne_r1 R₁.inputTape).symm
    rw [h4r1.2.1, h3r1.2.1]; simpa [hpre_ans_len] using hp2R1
  obtain ⟨t5, p5, l5, u5, n_5, tr5, hn5, hout5, ht5R1_abs, hp5R1, hw5, henv5⟩ :=
    lPhase_rewindLeft R₁ R₂ qRewR1Start qRewR1Check qRewR1Right (.inr (.inl R₁.start))
      (tR1 R₁.inputTape) w.length
      (by rfl) (by rfl) (by rfl)
      t4 p4 l4 u4 L_env U_env hw4 henv4 hLB1 (by omega) hp4R1
      (by rw [hw4_eq]; simp)
      (fun z h0 h1 => by rw [hw4_eq, dif_pos ⟨h0, by omega⟩]; simp)
  have ht5R1 : t5 (tR1 R₁.inputTape) = Turing.Tape.mk₁ (w.map some) := by
    apply tape_ext_absCell 0
    intro z
    rw [ht5R1_abs z, hw4_eq z, absCell_mk₁_zero]
  have h5_st : t5 tSt = Turing.Tape.mk₁ [] ∧ p5 tSt = 0 := by
    have h5 := hout5 tSt (ltape_st_ne_r1 R₁.inputTape)
    have h4 := hout4 tSt ltape_st_ne_ans
    exact ⟨by rw [h5.1, h4.1, ht3St], by rw [h5.2.1, h4.2.1, hp3St]⟩
  have h5_ans : t5 tAns = Turing.Tape.mk₁ [] ∧ p5 tAns = 0 := by
    have h5 := hout5 tAns (ltape_ans_ne_r1 R₁.inputTape)
    exact ⟨by rw [h5.1, ht4Ans], by rw [h5.2.1, hp4Ans]⟩
  have h5_r1_other : ∀ j : Fin R₁.tapeCount, j ≠ R₁.inputTape →
      t5 (tR1 j) = Turing.Tape.mk₁ [] ∧ p5 (tR1 j) = 0 := by
    intro j hj
    have hne : (tR1 j : LTape R₁.tapeCount R₂.tapeCount) ≠ tR1 R₁.inputTape := by simp [hj]
    have h5 := hout5 (tR1 j) hne
    have h4 := hout4 (tR1 j) (ltape_ans_ne_r1 j).symm
    have h3 := hout3 (tR1 j) (ltape_st_ne_r1 j).symm
    have h2 := hout2 (tR1 j) (ltape_ans_ne_r1 j).symm hne
    have h1 := hout1 (tR1 j) (ltape_st_ne_r1 j).symm hne
    have h0 := htR10 j
    exact ⟨by rw [h5.1, h4.1, h3.1, h2.1, h1.1, h0.1],
           by rw [h5.2.1, h4.2.1, h3.2.1, h2.2.1, h1.2.1, h0.2]⟩
  have h5_r2 : ∀ j : Fin R₂.tapeCount, t5 (tR2 j) = Turing.Tape.mk₁ [] ∧ p5 (tR2 j) = 0 := by
    intro j
    have h5 := hout5 (tR2 j) (ltape_r1_ne_r2 _ _).symm
    have h4 := hout4 (tR2 j) (ltape_ans_ne_r2 j).symm
    have h3 := hout3 (tR2 j) (ltape_st_ne_r2 j).symm
    have h2 := hout2 (tR2 j) (ltape_ans_ne_r2 j).symm (ltape_r1_ne_r2 _ _).symm
    have h1 := hout1 (tR2 j) (ltape_st_ne_r2 j).symm (ltape_r1_ne_r2 _ _).symm
    have h0 := htR20 j
    exact ⟨by rw [h5.1, h4.1, h3.1, h2.1, h1.1, h0.1],
           by rw [h5.2.1, h4.2.1, h3.2.1, h2.2.1, h1.2.1, h0.2]⟩
  obtain ⟨t6, p6, l6, u6, tr6, hout6, ht6in, ht6other, hp6, hw6, henv6⟩ :=
    lPhase_embed_R1 R₁ R₂ w out1 n1 B1 final1 ht1 hh1 ho1 hother1 hpos1 hbound1
      t5 p5 l5 u5 L_env U_env hLB hBU hw5 henv5 ht5R1
      (fun j hj => (h5_r1_other j hj).1)
      (fun j => by
        by_cases hj : j = R₁.inputTape
        · subst hj; exact hp5R1
        · exact (h5_r1_other j hj).2)
  have htr_12345 : Computation.Trace (locatedStep (loopMachine R₁ R₂))
      (n_1 + (n_2 + (n_3 + (n_4 + (n_5 + n1)))))
      (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qEncStCheck) t p l u)
      (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qBranchOut) t6 p6 l6 u6) :=
    trace_trans tr1 (trace_trans tr2 (trace_trans tr3 (trace_trans tr4 (trace_trans tr5 tr6))))
  have hlen_tot : n_1 + (n_2 + (n_3 + (n_4 + (n_5 + n1)))) = n1 + 13 * st.length + 9 * ans.length + 15 := by
    rw [hn1, hn2, hn3, hn4, hn5, hw_len]; omega
  refine ⟨t6, p6, l6, u6, n1 + 13 * st.length + 9 * ans.length + 15, hlen_tot ▸ htr_12345, rfl,
    ?_, ?_, ?_, ?_, ht6in, ht6other, hp6, ?_, hw6, henv6⟩
  · have := hout6 tSt (fun j => ltape_st_ne_r1 j); rw [this.1, h5_st.1]
  · have := hout6 tSt (fun j => ltape_st_ne_r1 j); rw [this.2.1, h5_st.2]
  · have := hout6 tAns (fun j => ltape_ans_ne_r1 j); rw [this.1, h5_ans.1]
  · have := hout6 tAns (fun j => ltape_ans_ne_r1 j); rw [this.2.1, h5_ans.2]
  · intro j
    have := hout6 (tR2 j) (fun k => (ltape_r1_ne_r2 k j).symm)
    exact ⟨by rw [this.1, (h5_r2 j).1], by rw [this.2.1, (h5_r2 j).2]⟩

private theorem lPhase_round_done
    (st ans outW : List Bool) (n1 B1 maxLen : ℕ) (final1 : LocatedCfg R₁)
    (ht1 : Computation.Trace (locatedStep R₁) n1
      (locatedInit R₁ (st.flatMap (fun b => [true, b]) ++ [false] ++ ans)) final1)
    (hh1 : ∃ b : Bool, final1.config.state = .inl b)
    (ho1 : final1.config.tapes R₁.inputTape = Turing.Tape.mk₁ ((true :: outW).map some))
    (hother1 : ∀ j : Fin R₁.tapeCount, j ≠ R₁.inputTape → final1.config.tapes j = Turing.Tape.mk₁ [])
    (hpos1 : ∀ j : Fin R₁.tapeCount, final1.position j = 0)
    (hbound1 : ∀ j : Fin R₁.tapeCount, -(B1 : ℤ) ≤ final1.lower j ∧ final1.upper j ≤ (B1 : ℤ))
    (hin_len : (st.flatMap (fun b => [true, b]) ++ [false] ++ ans).length ≤ maxLen)
    (hout_len : outW.length ≤ maxLen)
    (t : LCfg R₁.tapeCount R₂.tapeCount) (p l u : LPos R₁.tapeCount R₂.tapeCount)
    (B_env : ℕ)
    (hB1 : B1 ≤ B_env) (hMax : maxLen + 4 ≤ B_env)
    (hinv : LoopInv t p l u (-(B_env : ℤ)) (B_env : ℤ) R₁.inputTape R₂.inputTape st ans) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qEncStCheck) t p l u)
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inl true) t1 p1 l1 u1) ∧
      n ≤ n1 + 18 * maxLen + 28 ∧
      t1 tSt = Turing.Tape.mk₁ (outW.map some) ∧
      (∀ r, -(B_env : ℤ) ≤ l1 r ∧ u1 r ≤ (B_env : ℤ)) := by
  have hin_len' : ((st.flatMap (fun b => [true, b]) ++ [false] ++ ans).length : ℤ) ≤ (B_env : ℤ) := by omega
  obtain ⟨t1, p1, l1, u1, n_1, tr1, hn1, ht1St, hp1St, _, _, ht1in, _, hp1R1, _, hw1, henv1⟩ :=
    lPhase_run_R1 R₁ R₂ st ans (true :: outW) n1 B1 final1 ht1 hh1 ho1 hother1 hpos1 hbound1
      t p l u (-(B_env : ℤ)) (B_env : ℤ) (by omega) (by omega) (by omega) hin_len' hinv
  let in1 : LTape R₁.tapeCount R₂.tapeCount := tR1 R₁.inputTape
  have hhead : (t1 in1).head = some true := by
    rw [ht1in, List.map_cons]; rfl
  have hs0 := lStep_branch R₁ R₂ (q := qBranchOut) (k := in1) (by rfl) t1 p1 l1 u1 (hw1 in1)
  rw [hhead] at hs0
  have hs1 := lStep_move_right R₁ R₂ (q := qDoneAdv) (q' := qDoneCopyCheck) (k := in1)
    (by rfl) t1 p1 l1 u1
  let t_2 := Function.update t1 in1 ((t1 in1).move .right)
  let p_2 := Function.update p1 in1 (p1 in1 + 1)
  let l_2 := Function.update l1 in1 (min (l1 in1) (p1 in1 + 1))
  let u_2 := Function.update u1 in1 (max (u1 in1) (p1 in1 + 1))
  have hw2 : ∀ r, l_2 r ≤ p_2 r ∧ p_2 r ≤ u_2 r := by
    intro r; by_cases hr : r = in1
    · subst r; simp only [p_2, l_2, u_2, Function.update_self]; exact ⟨min_le_right _ _, le_max_right _ _⟩
    · simp only [p_2, l_2, u_2, Function.update_of_ne hr]; exact hw1 r
  have hp1_in1 : p1 in1 = 0 := hp1R1 R₁.inputTape
  have henv2 : ∀ r, -(B_env : ℤ) ≤ l_2 r ∧ u_2 r ≤ (B_env : ℤ) := by
    intro r; by_cases hr : r = in1
    · have h1' := henv1 in1
      dsimp only [l_2, u_2]; rw [hr]; simp only [Function.update_self, hp1_in1]
      exact ⟨le_min h1'.1 (by omega), max_le h1'.2 (by omega)⟩
    · simp only [l_2, u_2, Function.update_of_ne hr]; exact henv1 r
  have ht2S : ∀ z : ℤ, 1 ≤ z → absCell (t_2 in1) 1 z =
      if h : (z - 1).toNat < outW.length then some outW[(z - 1).toNat] else none := by
    intro z hz
    have heq : t_2 in1 = (t1 in1).move .right := by simp [t_2]
    conv_lhs => rw [heq, show (1 : ℤ) = 0 + 1 by rfl, absCell_move_right, ht1in, absCell_mk₁_zero]
    have hidx : 0 ≤ z ∧ z.toNat < (true :: outW).length ↔ (z - 1).toNat < outW.length := by
      simp; omega
    by_cases h1 : 0 ≤ z ∧ z.toNat < (true :: outW).length
    · have h2 : (z - 1).toNat < outW.length := hidx.mp h1
      rw [dif_pos h1, dif_pos h2]
      have hz_eq : z.toNat = (z - 1).toNat + 1 := by omega
      simp only [hz_eq, List.getElem_cons_succ]
    · have h2 : ¬ ((z - 1).toNat < outW.length) := fun h => h1 (hidx.mpr h)
      rw [dif_neg h1, dif_neg h2]
  obtain ⟨t3, p3, l3, u3, n_3, tr3, hn3, hout3, ht3in_abs, hp3in, ht3St, hp3St, hw3, henv3⟩ :=
    lPhase_copy R₁ R₂ qDoneCopyCheck qDoneCopyWT qDoneCopyWF qDoneCopyAdvD qDoneCopyAdvS qRewStDoneStart
      in1 tSt (ltape_st_ne_r1 R₁.inputTape).symm
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      [] outW 1 (by omega) t_2 p_2 l_2 u_2 (-(B_env : ℤ)) (B_env : ℤ) hw2 henv2 (by omega) (by simp; omega)
      (by simp [p_2, hp1_in1]) (by simp [p_2, hp1St]) ht2S
      ((isWordAt_zero_iff _ _).mpr (by simp [t_2, ht1St]))
  have ht3St' : IsWordAt (t3 tSt) (outW.length : ℤ) outW := by simpa using ht3St
  have hp3St' : p3 tSt = outW.length := by simpa using hp3St
  obtain ⟨t4, p4, l4, u4, n_4, tr4, hn4, hout4, ht4St_abs, hp4St, hw4, henv4⟩ :=
    lPhase_rewindLeft R₁ R₂ qRewStDoneStart qRewStDoneCheck qRewStDoneRight qEraseR1DoneStart
      tSt outW.length
      (by rfl) (by rfl) (by rfl)
      t3 p3 l3 u3 (-(B_env : ℤ)) (B_env : ℤ) hw3 henv3 (by omega) (by omega)
      hp3St'
      (by rw [ht3St']; simp)
      (fun z h0 h1 => by rw [ht3St', dif_pos ⟨h0, by omega⟩]; simp)
  have ht4St : t4 tSt = Turing.Tape.mk₁ (outW.map some) := by
    apply tape_ext_absCell 0
    intro z
    rw [ht4St_abs z, ht3St' z, absCell_mk₁_zero]
  have ht4in_abs : ∀ z : ℤ, absCell (t4 in1) ((1 + outW.length : ℕ) : ℤ) z = none ↔
      ¬ (0 ≤ z ∧ z < ((1 + outW.length : ℕ) : ℤ)) := by
    intro z
    have h4eq := hout4 in1 (ltape_st_ne_r1 R₁.inputTape).symm
    rw [h4eq.1, show ((1 + outW.length : ℕ) : ℤ) = 1 + (outW.length : ℤ) by omega, ht3in_abs z,
      show t_2 in1 = (t1 in1).move .right from by simp [t_2],
      show (1 : ℤ) = 0 + 1 by rfl, absCell_move_right, ht1in, absCell_mk₁_eq_none]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; constructor <;> omega
  have hp4in : p4 in1 = ((1 + outW.length : ℕ) : ℤ) := by
    have h4eq := hout4 in1 (ltape_st_ne_r1 R₁.inputTape).symm
    rw [h4eq.2.1, hp3in]; omega
  obtain ⟨t5, p5, l5, u5, n_5, tr5, hn5, hout5, _, _, hw5, henv5⟩ :=
    lPhase_eraseLeft R₁ R₂ qEraseR1DoneStart qEraseR1DoneCheck qEraseR1DoneW qEraseR1DoneRight qHalt
      in1 (1 + outW.length)
      (by rfl) (by rfl) (by rfl) (by rfl)
      t4 p4 l4 u4 (-(B_env : ℤ)) (B_env : ℤ) hw4 henv4 (by omega) (by omega) hp4in ht4in_abs
  have hs_halt := lStep_halt R₁ R₂ (q := qHalt) (b := true) (by rfl) t5 p5 l5 u5
  have htr_all := trace_trans tr1 (trace_prepend2 hs0 hs1 (trace_trans tr3 (trace_trans tr4 (trace_trans tr5 (.cons hs_halt (.refl _))))))
  have hlen_w : (st.flatMap (fun b => [true, b]) ++ [false] ++ ans).length = 2 * st.length + 1 + ans.length := by
    rw [List.length_append, List.length_append, List.length_singleton, list_flatMap_pair_length]
  refine ⟨t5, p5, l5, u5, n_1 + (2 + (n_3 + (n_4 + (n_5 + 1)))), htr_all, ?_, ?_, fun r => henv5 r⟩
  · rw [hn1, hn3, hn4, hn5]; omega
  · have h5eq := hout5 tSt (ltape_st_ne_r1 R₁.inputTape)
    rw [h5eq.1, ht4St]

private theorem lPhase_round_cont
    (st ans st' q ans' : List Bool) (n1 B1 n2 B2 maxLen : ℕ)
    (final1 : LocatedCfg R₁) (final2 : LocatedCfg R₂)
    (ht1 : Computation.Trace (locatedStep R₁) n1
      (locatedInit R₁ (st.flatMap (fun b => [true, b]) ++ [false] ++ ans)) final1)
    (hh1 : ∃ b : Bool, final1.config.state = .inl b)
    (ho1 : final1.config.tapes R₁.inputTape =
      Turing.Tape.mk₁ ((false :: (st'.flatMap (fun b => [true, b]) ++ [false] ++ q)).map some))
    (hother1 : ∀ j : Fin R₁.tapeCount, j ≠ R₁.inputTape → final1.config.tapes j = Turing.Tape.mk₁ [])
    (hpos1 : ∀ j : Fin R₁.tapeCount, final1.position j = 0)
    (hbound1 : ∀ j : Fin R₁.tapeCount, -(B1 : ℤ) ≤ final1.lower j ∧ final1.upper j ≤ (B1 : ℤ))
    (ht2 : Computation.Trace (locatedStep R₂) n2 (locatedInit R₂ q) final2)
    (hh2 : ∃ b : Bool, final2.config.state = .inl b)
    (ho2 : final2.config.tapes R₂.inputTape = Turing.Tape.mk₁ (ans'.map some))
    (hother2 : ∀ j : Fin R₂.tapeCount, j ≠ R₂.inputTape → final2.config.tapes j = Turing.Tape.mk₁ [])
    (hpos2 : ∀ j : Fin R₂.tapeCount, final2.position j = 0)
    (hbound2 : ∀ j : Fin R₂.tapeCount, -(B2 : ℤ) ≤ final2.lower j ∧ final2.upper j ≤ (B2 : ℤ))
    (hin_len : (st.flatMap (fun b => [true, b]) ++ [false] ++ ans).length ≤ maxLen)
    (hmid_len : (st'.flatMap (fun b => [true, b]) ++ [false] ++ q).length ≤ maxLen)
    (hans'_len : ans'.length ≤ maxLen)
    (t : LCfg R₁.tapeCount R₂.tapeCount) (p l u : LPos R₁.tapeCount R₂.tapeCount)
    (B_env : ℕ)
    (hB1 : B1 ≤ B_env) (hB2 : B2 ≤ B_env) (hMax : maxLen + 4 ≤ B_env)
    (hinv : LoopInv t p l u (-(B_env : ℤ)) (B_env : ℤ) R₁.inputTape R₂.inputTape st ans) :
    ∃ t1 p1 l1 u1 n,
      Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qEncStCheck) t p l u)
        (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qEncStCheck) t1 p1 l1 u1) ∧
      n ≤ n1 + n2 + 27 * maxLen + 42 ∧
      LoopInv t1 p1 l1 u1 (-(B_env : ℤ)) (B_env : ℤ) R₁.inputTape R₂.inputTape st' ans' := by
  have hin_len' : ((st.flatMap (fun b => [true, b]) ++ [false] ++ ans).length : ℤ) ≤ (B_env : ℤ) := by omega
  obtain ⟨t1, p1, l1, u1, n_1, tr1, hn1, ht1St, hp1St, ht1Ans, hp1Ans, ht1in, ht1r1_other, hp1R1, ht1r2, hw1, henv1⟩ :=
    lPhase_run_R1 R₁ R₂ st ans (false :: (st'.flatMap (fun b => [true, b]) ++ [false] ++ q))
      n1 B1 final1 ht1 hh1 ho1 hother1 hpos1 hbound1
      t p l u (-(B_env : ℤ)) (B_env : ℤ) (by omega) (by omega) (by omega) hin_len' hinv
  let in1 : LTape R₁.tapeCount R₂.tapeCount := tR1 R₁.inputTape
  let in2 : LTape R₁.tapeCount R₂.tapeCount := tR2 R₂.inputTape
  have hmid_parts : (st'.flatMap (fun b => [true, b]) ++ [false] ++ q).length = 2 * st'.length + 1 + q.length := by
    rw [List.length_append, List.length_append, List.length_singleton, list_flatMap_pair_length]
  have hlen_in : (st.flatMap (fun b => [true, b]) ++ [false] ++ ans).length = 2 * st.length + 1 + ans.length := by
    rw [List.length_append, List.length_append, List.length_singleton, list_flatMap_pair_length]
  have ht1_in2 : t1 in2 = Turing.Tape.mk₁ [] ∧ p1 in2 = 0 := ht1r2 R₂.inputTape
  let fw := false :: (st'.flatMap (fun b => [true, b]) ++ [false] ++ q)
  have hfw_len : fw.length = 2 * st'.length + 2 + q.length := by dsimp [fw]; rw [hmid_parts]; omega
  have hhead : (t1 in1).head = some false := by rw [ht1in, List.map_cons]; rfl
  have hs0 := lStep_branch R₁ R₂ (q := qBranchOut) (k := in1) (by rfl) t1 p1 l1 u1 (hw1 in1)
  rw [hhead] at hs0
  have hs1 := lStep_move_right R₁ R₂ (q := qDecAdv) (q' := qDecCheck1) (k := in1)
    (by rfl) t1 p1 l1 u1
  let t_2 := Function.update t1 in1 ((t1 in1).move .right)
  let p_2 := Function.update p1 in1 (p1 in1 + 1)
  let l_2 := Function.update l1 in1 (min (l1 in1) (p1 in1 + 1))
  let u_2 := Function.update u1 in1 (max (u1 in1) (p1 in1 + 1))
  have hw2 : ∀ r, l_2 r ≤ p_2 r ∧ p_2 r ≤ u_2 r := by
    intro r; by_cases hr : r = in1
    · subst r; simp only [p_2, l_2, u_2, Function.update_self]; exact ⟨min_le_right _ _, le_max_right _ _⟩
    · simp only [p_2, l_2, u_2, Function.update_of_ne hr]; exact hw1 r
  have hp1_in1 : p1 in1 = 0 := hp1R1 R₁.inputTape
  have henv2 : ∀ r, -(B_env : ℤ) ≤ l_2 r ∧ u_2 r ≤ (B_env : ℤ) := by
    intro r; by_cases hr : r = in1
    · have h1' := henv1 in1
      dsimp only [l_2, u_2]; rw [hr]; simp only [Function.update_self, hp1_in1]
      exact ⟨le_min h1'.1 (by omega), max_le h1'.2 (by omega)⟩
    · simp only [l_2, u_2, Function.update_of_ne hr]; exact henv1 r
  have ht2in : ∀ z : ℤ, absCell (t_2 in1) 1 z = absCell (Turing.Tape.mk₁ (fw.map some)) 0 z := by
    intro z
    rw [show t_2 in1 = (t1 in1).move .right from by simp [t_2],
      show (1 : ℤ) = 0 + 1 by rfl, absCell_move_right, ht1in]
  obtain ⟨t3, p3, l3, u3, n_3, tr3, hn3, hout3, ht3in, hp3in, ht3St, hp3St, hw3, henv3⟩ :=
    lPhase_decPairs R₁ R₂ st' q t_2 p_2 l_2 u_2 (-(B_env : ℤ)) (B_env : ℤ) hw2 henv2
      (by omega) (by omega) (by dsimp only [p_2, in1]; simp [hp1R1 R₁.inputTape])
      (by simp [p_2, hp1St]) ht2in
      (by simp [t_2, ht1St])
  have hne_in1_in2 : (in1 : LTape R₁.tapeCount R₂.tapeCount) ≠ in2 := ltape_r1_ne_r2 _ _
  have ho3_in2 := hout3 in2 hne_in1_in2.symm (ltape_st_ne_r2 R₂.inputTape).symm
  have ht3S_q : ∀ z : ℤ, ((2 * st'.length + 2 : ℕ) : ℤ) ≤ z →
      absCell (t3 in1) ((2 * st'.length + 2 : ℕ) : ℤ) z =
        if h : (z - ((2 * st'.length + 2 : ℕ) : ℤ)).toNat < q.length then
          some q[(z - ((2 * st'.length + 2 : ℕ) : ℤ)).toNat] else none := by
    intro z hz
    rw [ht3in z, show (false :: (st'.flatMap (fun b => [true, b]) ++ [false] ++ q)) = fw from rfl,
      absCell_mk₁_zero]
    have hq_fw : 0 ≤ z ∧ z.toNat < fw.length ↔ (z - ((2 * st'.length + 2 : ℕ) : ℤ)).toNat < q.length := by
      rw [hfw_len]; omega
    by_cases h1 : 0 ≤ z ∧ z.toNat < fw.length
    · have h2 : (z - ((2 * st'.length + 2 : ℕ) : ℤ)).toNat < q.length := hq_fw.mp h1
      rw [dif_pos h1, dif_pos h2]
      have hz_eq : z.toNat = (2 * st'.length + 1 + (z - ((2 * st'.length + 2 : ℕ) : ℤ)).toNat) + 1 := by omega
      have hpre_l : (st'.flatMap (fun b => [true, b]) ++ [false]).length = 2 * st'.length + 1 := by
        rw [List.length_append, List.length_singleton, list_flatMap_pair_length]
      have hg' : (st'.flatMap (fun b => [true, b]) ++ [false] ++ q)[2 * st'.length + 1 +
          (z - ((2 * st'.length + 2 : ℕ) : ℤ)).toNat]'(by rw [hmid_parts]; omega) =
          q[(z - ((2 * st'.length + 2 : ℕ) : ℤ)).toNat] := by
        rw [List.getElem_append_right (by omega)]
        simp [hpre_l]
      have hget : fw[z.toNat]'h1.2 = q[(z - ((2 * st'.length + 2 : ℕ) : ℤ)).toNat]'h2 := by
        simp only [hz_eq]; dsimp [fw]; exact hg'
      exact congrArg some hget
    · have h2 : ¬ ((z - ((2 * st'.length + 2 : ℕ) : ℤ)).toNat < q.length) := fun h => h1 (hq_fw.mpr h)
      rw [dif_neg h1, dif_neg h2]
  obtain ⟨t4, p4, l4, u4, n_4, tr4, hn4, hout4, ht4in_abs, hp4in, ht4in2, hp4in2, hw4, henv4⟩ :=
    lPhase_copy R₁ R₂ qDecQCheck qDecQWT qDecQWF qDecQAdvD qDecQAdvS qRewStDecStart
      in1 in2 hne_in1_in2
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      [] q ((2 * st'.length + 2 : ℕ) : ℤ) (by omega) t3 p3 l3 u3 (-(B_env : ℤ)) (B_env : ℤ)
      hw3 henv3 (by omega) (by simp; omega) hp3in
      (by rw [ho3_in2.2.1]; dsimp only [p_2, in2]; rw [Function.update_of_ne hne_in1_in2.symm]; exact (ht1r2 R₂.inputTape).2)
      ht3S_q
      ((isWordAt_zero_iff _ _).mpr (by rw [ho3_in2.1]; dsimp only [t_2, in2]; rw [Function.update_of_ne hne_in1_in2.symm]; exact (ht1r2 R₂.inputTape).1))
  have ho4_st := hout4 tSt (ltape_st_ne_r1 R₁.inputTape) (ltape_st_ne_r2 R₂.inputTape)
  have ht4St : IsWordAt (t4 tSt) (st'.length : ℤ) st' := by rw [ho4_st.1]; exact ht3St
  have hp4St : p4 tSt = st'.length := by rw [ho4_st.2.1, hp3St]
  obtain ⟨t5, p5, l5, u5, n_5, tr5, hn5, hout5, ht5St_abs, hp5St, hw5, henv5⟩ :=
    lPhase_rewindLeft R₁ R₂ qRewStDecStart qRewStDecCheck qRewStDecRight qRewR2DecStart
      tSt st'.length
      (by rfl) (by rfl) (by rfl)
      t4 p4 l4 u4 (-(B_env : ℤ)) (B_env : ℤ) hw4 henv4 (by omega) (by omega) hp4St
      (by rw [ht4St]; simp) (fun z h0 h1 => by rw [ht4St, dif_pos ⟨h0, by omega⟩]; simp)
  have ht5St : t5 tSt = Turing.Tape.mk₁ (st'.map some) := by
    apply tape_ext_absCell 0; intro z; rw [ht5St_abs z, ht4St z, absCell_mk₁_zero]
  have ho5_in2 := hout5 in2 (ltape_st_ne_r2 R₂.inputTape).symm
  have ht5in2 : IsWordAt (t5 in2) (q.length : ℤ) q := by rw [ho5_in2.1]; simpa using ht4in2
  have hp5in2 : p5 in2 = q.length := by rw [ho5_in2.2.1]; simpa using hp4in2
  obtain ⟨t6, p6, l6, u6, n_6, tr6, hn6, hout6, ht6in2_abs, hp6in2, hw6, henv6⟩ :=
    lPhase_rewindLeft R₁ R₂ qRewR2DecStart qRewR2DecCheck qRewR2DecRight qEraseR1DecStart
      in2 q.length
      (by rfl) (by rfl) (by rfl)
      t5 p5 l5 u5 (-(B_env : ℤ)) (B_env : ℤ) hw5 henv5 (by omega) (by omega) hp5in2
      (by rw [ht5in2]; simp) (fun z h0 h1 => by rw [ht5in2, dif_pos ⟨h0, by omega⟩]; simp)
  have ht6in2 : t6 in2 = Turing.Tape.mk₁ (q.map some) := by
    apply tape_ext_absCell 0; intro z; rw [ht6in2_abs z, ht5in2 z, absCell_mk₁_zero]
  have ho6_in1 := hout6 in1 hne_in1_in2
  have ho5_in1 := hout5 in1 (ltape_st_ne_r1 R₁.inputTape).symm
  have ht6in1_abs : ∀ z : ℤ, absCell (t6 in1) (fw.length : ℤ) z = none ↔ ¬ (0 ≤ z ∧ z < (fw.length : ℤ)) := by
    intro z
    rw [ho6_in1.1, ho5_in1.1,
      show (fw.length : ℤ) = ((2 * st'.length + 2 : ℕ) : ℤ) + (q.length : ℤ) by rw [hfw_len]; omega,
      ht4in_abs z, ht3in z,
      show (false :: (st'.flatMap (fun b => [true, b]) ++ [false] ++ q)) = fw from rfl,
      absCell_mk₁_eq_none, hfw_len]
    constructor <;> omega
  have hp6in1 : p6 in1 = fw.length := by
    rw [ho6_in1.2.1, ho5_in1.2.1, hp4in]; omega
  obtain ⟨t7, p7, l7, u7, n_7, tr7, hn7, hout7, ht7in1, hp7in1, hw7, henv7⟩ :=
    lPhase_eraseLeft R₁ R₂ qEraseR1DecStart qEraseR1DecCheck qEraseR1DecW qEraseR1DecRight (.inr (.inr R₂.start))
      in1 fw.length
      (by rfl) (by rfl) (by rfl) (by rfl)
      t6 p6 l6 u6 (-(B_env : ℤ)) (B_env : ℤ) hw6 henv6 (by omega) (by omega) hp6in1 ht6in1_abs
  have ho7_in2 := hout7 in2 hne_in1_in2.symm
  have ht7r2_other : ∀ j : Fin R₂.tapeCount, j ≠ R₂.inputTape →
      t7 (tR2 j) = Turing.Tape.mk₁ [] ∧ p7 (tR2 j) = 0 := by
    intro j hj
    have hne : (tR2 j : LTape R₁.tapeCount R₂.tapeCount) ≠ in2 := by simp [in2, hj]
    have h7 := hout7 (tR2 j) (ltape_r1_ne_r2 _ _).symm
    have h6 := hout6 (tR2 j) hne
    have h5 := hout5 (tR2 j) (ltape_st_ne_r2 j).symm
    have h4 := hout4 (tR2 j) (ltape_r1_ne_r2 _ _).symm hne
    have h3 := hout3 (tR2 j) (ltape_r1_ne_r2 _ _).symm (ltape_st_ne_r2 j).symm
    have h0 := ht1r2 j
    exact ⟨by rw [h7.1, h6.1, h5.1, h4.1, h3.1]; simp [t_2]; exact h0.1,
           by rw [h7.2.1, h6.2.1, h5.2.1, h4.2.1, h3.2.1]; simp [p_2]; exact h0.2⟩
  obtain ⟨t8, p8, l8, u8, tr8, hout8, ht8in2, ht8r2_other, hp8R2, hw8, henv8⟩ :=
    lPhase_embed_R2 R₁ R₂ q ans' n2 B2 final2 ht2 hh2 ho2 hother2 hpos2 hbound2
      t7 p7 l7 u7 (-(B_env : ℤ)) (B_env : ℤ) (by omega) (by omega) hw7 henv7
      (by rw [ho7_in2.1, ht6in2])
      (fun j hj => (ht7r2_other j hj).1)
      (fun j => by
        by_cases hj : j = R₂.inputTape
        · subst hj; rw [ho7_in2.2.1, hp6in2]
        · exact (ht7r2_other j hj).2)
  have ho8_ans := hout8 tAns (fun j => ltape_ans_ne_r2 j)
  have ht8Ans : t8 tAns = Turing.Tape.mk₁ [] := by
    have h7 := hout7 tAns (ltape_ans_ne_r1 R₁.inputTape)
    have h6 := hout6 tAns (ltape_ans_ne_r2 R₂.inputTape)
    have h5 := hout5 tAns ltape_st_ne_ans.symm
    have h4 := hout4 tAns (ltape_ans_ne_r1 R₁.inputTape) (ltape_ans_ne_r2 R₂.inputTape)
    have h3 := hout3 tAns (ltape_ans_ne_r1 R₁.inputTape) ltape_st_ne_ans.symm
    rw [ho8_ans.1, h7.1, h6.1, h5.1, h4.1, h3.1]; simp [t_2, ht1Ans]
  have hp8Ans : p8 tAns = 0 := by
    have h7 := hout7 tAns (ltape_ans_ne_r1 R₁.inputTape)
    have h6 := hout6 tAns (ltape_ans_ne_r2 R₂.inputTape)
    have h5 := hout5 tAns ltape_st_ne_ans.symm
    have h4 := hout4 tAns (ltape_ans_ne_r1 R₁.inputTape) (ltape_ans_ne_r2 R₂.inputTape)
    have h3 := hout3 tAns (ltape_ans_ne_r1 R₁.inputTape) ltape_st_ne_ans.symm
    rw [ho8_ans.2.1, h7.2.1, h6.2.1, h5.2.1, h4.2.1, h3.2.1]; simp [p_2, hp1Ans]
  obtain ⟨t9, p9, l9, u9, n_9, tr9, hn9, hout9, ht9in2_abs, hp9in2, ht9Ans, hp9Ans, hw9, henv9⟩ :=
    lPhase_copy R₁ R₂ qRetAnsCheck qRetAnsWT qRetAnsWF qRetAnsAdvD qRetAnsAdvS qRewAnsRetStart
      in2 tAns (ltape_ans_ne_r2 R₂.inputTape).symm
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      [] ans' 0 (le_refl _) t8 p8 l8 u8 (-(B_env : ℤ)) (B_env : ℤ) hw8 henv8 (by omega) (by simp; omega)
      (hp8R2 R₂.inputTape) hp8Ans
      (fun z hz => by
        rw [ht8in2, absCell_mk₁_zero]
        split_ifs with h1 h2
        · simp
        · exfalso; exact h2 (by omega)
        · exfalso; exact h1 (by omega)
        · rfl)
      ((isWordAt_zero_iff _ _).mpr ht8Ans)
  have ht9Ans' : IsWordAt (t9 tAns) (ans'.length : ℤ) ans' := by simpa using ht9Ans
  have hp9Ans' : p9 tAns = ans'.length := by simpa using hp9Ans
  obtain ⟨t10, p10, l10, u10, n_10, tr10, hn10, hout10, ht10Ans_abs, hp10Ans, hw10, henv10⟩ :=
    lPhase_rewindLeft R₁ R₂ qRewAnsRetStart qRewAnsRetCheck qRewAnsRetRight qEraseR2RetStart
      tAns ans'.length
      (by rfl) (by rfl) (by rfl)
      t9 p9 l9 u9 (-(B_env : ℤ)) (B_env : ℤ) hw9 henv9 (by omega) (by omega)
      hp9Ans'
      (by rw [ht9Ans']; simp) (fun z h0 h1 => by rw [ht9Ans', dif_pos ⟨h0, by omega⟩]; simp)
  have ht10Ans : t10 tAns = Turing.Tape.mk₁ (ans'.map some) := by
    apply tape_ext_absCell 0; intro z; rw [ht10Ans_abs z, ht9Ans' z, absCell_mk₁_zero]
  have ho10_in2 := hout10 in2 (ltape_ans_ne_r2 R₂.inputTape).symm
  have ht10in2_abs : ∀ z : ℤ, absCell (t10 in2) (ans'.length : ℤ) z = none ↔ ¬ (0 ≤ z ∧ z < (ans'.length : ℤ)) := by
    intro z
    rw [ho10_in2.1, show (ans'.length : ℤ) = 0 + (ans'.length : ℤ) by omega, ht9in2_abs z,
      ht8in2, absCell_mk₁_eq_none]; simp
  have hp10in2 : p10 in2 = ans'.length := by rw [ho10_in2.2.1]; simpa using hp9in2
  obtain ⟨t11, p11, l11, u11, n_11, tr11, hn11, hout11, ht11in2, hp11in2, hw11, henv11⟩ :=
    lPhase_eraseLeft R₁ R₂ qEraseR2RetStart qEraseR2RetCheck qEraseR2RetW qEraseR2RetRight qEncStCheck
      in2 ans'.length
      (by rfl) (by rfl) (by rfl) (by rfl)
      t10 p10 l10 u10 (-(B_env : ℤ)) (B_env : ℤ) hw10 henv10 (by omega) (by omega) hp10in2 ht10in2_abs
  have ht11St : t11 tSt = Turing.Tape.mk₁ (st'.map some) ∧ p11 tSt = 0 := by
    have h11 := hout11 tSt (ltape_st_ne_r2 R₂.inputTape)
    have h10 := hout10 tSt ltape_st_ne_ans
    have h9 := hout9 tSt (ltape_st_ne_r2 R₂.inputTape) ltape_st_ne_ans
    have h8 := hout8 tSt (fun j => ltape_st_ne_r2 j)
    have h7 := hout7 tSt (ltape_st_ne_r1 R₁.inputTape)
    have h6 := hout6 tSt (ltape_st_ne_r2 R₂.inputTape)
    exact ⟨by rw [h11.1, h10.1, h9.1, h8.1, h7.1, h6.1, ht5St],
           by rw [h11.2.1, h10.2.1, h9.2.1, h8.2.1, h7.2.1, h6.2.1, hp5St]⟩
  have ht11Ans : t11 tAns = Turing.Tape.mk₁ (ans'.map some) ∧ p11 tAns = 0 := by
    have h11 := hout11 tAns (ltape_ans_ne_r2 R₂.inputTape)
    exact ⟨by rw [h11.1, ht10Ans], by rw [h11.2.1, hp10Ans]⟩
  have ht11r1 : ∀ j, t11 (tR1 j) = Turing.Tape.mk₁ [] ∧ p11 (tR1 j) = 0 := by
    intro j
    have h11 := hout11 (tR1 j) (ltape_r1_ne_r2 _ _)
    have h10 := hout10 (tR1 j) (ltape_ans_ne_r1 j).symm
    have h9 := hout9 (tR1 j) (ltape_r1_ne_r2 _ _) (ltape_ans_ne_r1 j).symm
    have h8 := hout8 (tR1 j) (fun k => ltape_r1_ne_r2 j k)
    by_cases hj : j = R₁.inputTape
    · subst hj
      exact ⟨by rw [h11.1, h10.1, h9.1, h8.1, ht7in1],
             by rw [h11.2.1, h10.2.1, h9.2.1, h8.2.1, hp7in1]⟩
    · have hne : (tR1 j : LTape R₁.tapeCount R₂.tapeCount) ≠ in1 := by simp [in1, hj]
      have h7 := hout7 (tR1 j) hne
      have h6 := hout6 (tR1 j) (ltape_r1_ne_r2 _ _)
      have h5 := hout5 (tR1 j) (ltape_st_ne_r1 j).symm
      have h4 := hout4 (tR1 j) hne (ltape_r1_ne_r2 _ _)
      have h3 := hout3 (tR1 j) hne (ltape_st_ne_r1 j).symm
      have h0 := ht1r1_other j hj
      exact ⟨by rw [h11.1, h10.1, h9.1, h8.1, h7.1, h6.1, h5.1, h4.1, h3.1]; simp [t_2, hne, h0],
             by rw [h11.2.1, h10.2.1, h9.2.1, h8.2.1, h7.2.1, h6.2.1, h5.2.1, h4.2.1, h3.2.1]; simp [p_2, hne, hp1R1 j]⟩
  have ht11r2 : ∀ j, t11 (tR2 j) = Turing.Tape.mk₁ [] ∧ p11 (tR2 j) = 0 := by
    intro j
    by_cases hj : j = R₂.inputTape
    · subst hj; exact ⟨ht11in2, hp11in2⟩
    · have hne : (tR2 j : LTape R₁.tapeCount R₂.tapeCount) ≠ in2 := by simp [in2, hj]
      have h11 := hout11 (tR2 j) hne
      have h10 := hout10 (tR2 j) (ltape_ans_ne_r2 j).symm
      have h9 := hout9 (tR2 j) hne (ltape_ans_ne_r2 j).symm
      have h0 := ht8r2_other j hj
      exact ⟨by rw [h11.1, h10.1, h9.1, h0], by rw [h11.2.1, h10.2.1, h9.2.1, hp8R2 j]⟩
  have htr_all := trace_trans tr1 (trace_prepend2 hs0 hs1 (trace_trans tr3 (trace_trans tr4
    (trace_trans tr5 (trace_trans tr6 (trace_trans tr7 (trace_trans tr8 (trace_trans tr9 (trace_trans tr10 tr11)))))))))

  refine ⟨t11, p11, l11, u11, _, htr_all, ?_,
    ht11St.1, ht11St.2, ht11Ans.1, ht11Ans.2, ht11r1, ht11r2, hw11, henv11⟩
  rw [hn1, hn3, hn4, hn5, hn6, hn7, hn9, hn10, hn11, hfw_len]; omega

private theorem lPhase_rounds
    (step : List Bool → List Bool)
    (Ms : PrimitiveMachine) (outs : Fin Ms.tapeCount) (Ks : ℕ)
    (hMs : ∀ w : List Bool, RunsWithin Ms outs w (step w) (polyBound Ks w.length) (polyBound Ks w.length))
    (O : PrimitiveMachine) (outO : Fin O.tapeCount)
    (R₁ : PrimitiveMachine) (C₁ : ℕ) (hC₁ : 1 ≤ C₁)
    (hR₁ : ∀ (input output : List Bool) (τ σ : ℝ), 0 ≤ τ → 0 ≤ σ →
      RunsWithin Ms outs input output τ σ →
      ∃ (n B : ℕ) (final : LocatedCfg R₁),
        Computation.Trace (locatedStep R₁) n (locatedInit R₁ input) final ∧
        (∃ b : Bool, final.config.state = .inl b) ∧
        final.config.tapes R₁.inputTape = Turing.Tape.mk₁ (output.map some) ∧
        (∀ j : Fin R₁.tapeCount, j ≠ R₁.inputTape → final.config.tapes j = Turing.Tape.mk₁ []) ∧
        (∀ j : Fin R₁.tapeCount, final.position j = 0) ∧
        (n : ℝ) ≤ (C₁ : ℝ) * (τ + σ + 1) ∧
        (B : ℝ) ≤ (C₁ : ℝ) * (σ + 1) ∧
        (∀ j : Fin R₁.tapeCount, -(B : ℤ) ≤ final.lower j ∧ final.upper j ≤ (B : ℤ)))
    (R₂ : PrimitiveMachine) (C₂ : ℕ) (hC₂ : 1 ≤ C₂)
    (hR₂ : ∀ (input output : List Bool) (τ σ : ℝ), 0 ≤ τ → 0 ≤ σ →
      RunsWithin O outO input output τ σ →
      ∃ (n B : ℕ) (final : LocatedCfg R₂),
        Computation.Trace (locatedStep R₂) n (locatedInit R₂ input) final ∧
        (∃ b : Bool, final.config.state = .inl b) ∧
        final.config.tapes R₂.inputTape = Turing.Tape.mk₁ (output.map some) ∧
        (∀ j : Fin R₂.tapeCount, j ≠ R₂.inputTape → final.config.tapes j = Turing.Tape.mk₁ []) ∧
        (∀ j : Fin R₂.tapeCount, final.position j = 0) ∧
        (n : ℝ) ≤ (C₂ : ℝ) * (τ + σ + 1) ∧
        (B : ℝ) ≤ (C₂ : ℝ) * (σ + 1) ∧
        (∀ j : Fin R₂.tapeCount, -(B : ℤ) ≤ final.lower j ∧ final.upper j ≤ (B : ℤ)))
    (τO σO : ℝ) (hτO : 0 ≤ τO) (hσO : 0 ≤ σO) (maxLen : ℕ) :
    let pairWord : List Bool → List Bool → List Bool := fun x y =>
      x.flatMap (fun b => [true, b]) ++ [false] ++ y
    let loopRuns : ℕ → List Bool → List Bool → List Bool → ℕ → Prop :=
      Nat.rec (motive := fun _ => List Bool → List Bool → List Bool → ℕ → Prop)
        (fun _ _ _ _ => False)
        (fun _ prev st ans outW ml =>
          (step (pairWord st ans) = true :: outW ∧
            (pairWord st ans).length ≤ ml ∧ outW.length ≤ ml) ∨
          (∃ st' q ans',
            step (pairWord st ans) = false :: pairWord st' q ∧
            (pairWord st ans).length ≤ ml ∧
            (pairWord st' q).length ≤ ml ∧
            ans'.length ≤ ml ∧
            RunsWithin O outO q ans' τO σO ∧
            prev st' ans' outW ml))
    let B_env := C₁ * (Nat.ceil (polyBound Ks maxLen) + 1) + C₂ * (Nat.ceil σO + 1) + maxLen + 4
    ∀ (rounds : ℕ) (st ans outW : List Bool)
      (t : LCfg R₁.tapeCount R₂.tapeCount) (p l u : LPos R₁.tapeCount R₂.tapeCount),
      1 ≤ rounds →
      loopRuns rounds st ans outW maxLen →
      LoopInv t p l u (-(B_env : ℤ)) (B_env : ℤ) R₁.inputTape R₂.inputTape st ans →
      ∃ t1 p1 l1 u1 n,
        Computation.Trace (locatedStep (loopMachine R₁ R₂)) n
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inr qEncStCheck) t p l u)
          (cCfg (loopOps R₁ R₂) qEncStCheck tSt (.inl true) t1 p1 l1 u1) ∧
        (n : ℝ) ≤ (rounds : ℝ) * ((C₁ : ℝ) * (2 * polyBound Ks maxLen + 1) +
          (C₂ : ℝ) * (τO + σO + 1) + 27 * (maxLen : ℝ) + 42) ∧
        t1 tSt = Turing.Tape.mk₁ (outW.map some) ∧
        (∀ r, -(B_env : ℤ) ≤ l1 r ∧ u1 r ≤ (B_env : ℤ)) := by
  intro pairWord loopRuns B_env rounds
  induction rounds with
  | zero => intro _ _ _ _ _ _ h1 _; omega
  | succ rounds ih =>
    intro st ans outW t p l u _ hrun hinv
    have hpb_nn : 0 ≤ polyBound Ks maxLen := polyBound_nonneg Ks maxLen
    rcases hrun with ⟨hst, hin_len, hout_len⟩ | ⟨st', q, ans', hst, hin_len, hmid_len, hans'_len, hO, hprev⟩
    · let pw := pairWord st ans
      have hpw_pb : polyBound Ks pw.length ≤ polyBound Ks maxLen := polyBound_mono Ks pw.length maxLen hin_len
      have hMs_run := hMs pw
      rw [hst] at hMs_run
      obtain ⟨n1, B1, final1, ht1, hh1, ho1, hother1, hpos1, hn1, hB1, hbound1⟩ :=
        hR₁ pw (true :: outW) (polyBound Ks pw.length) (polyBound Ks pw.length)
          (polyBound_nonneg Ks pw.length) (polyBound_nonneg Ks pw.length) hMs_run
      have hB1_le : B1 ≤ B_env := by
        have h1 : (B1 : ℝ) ≤ ((C₁ * (Nat.ceil (polyBound Ks maxLen) + 1) : ℕ) : ℝ) := by
          push_cast
          have hc : polyBound Ks pw.length ≤ (Nat.ceil (polyBound Ks maxLen) : ℝ) :=
            le_trans hpw_pb (Nat.le_ceil _)
          nlinarith [Nat.le_ceil (polyBound Ks maxLen)]
        exact Nat.le_trans (by exact_mod_cast h1) (by omega)
      obtain ⟨t1, p1, l1, u1, n, htr, hn_le, ht1St, henv1⟩ :=
        lPhase_round_done R₁ R₂ st ans outW n1 B1 maxLen final1 ht1 hh1 ho1 hother1 hpos1 hbound1
          hin_len hout_len t p l u B_env hB1_le (by omega) hinv
      refine ⟨t1, p1, l1, u1, n, htr, ?_, ht1St, henv1⟩
      have hn_real : (n : ℝ) ≤ (n1 : ℝ) + 18 * (maxLen : ℝ) + 28 := by exact_mod_cast hn_le
      have hc0 : (0 : ℝ) ≤ (C₂ : ℝ) * (τO + σO + 1) := by positivity
      have hn1' : (n1 : ℝ) ≤ (C₁ : ℝ) * (2 * polyBound Ks maxLen + 1) := by have hC1_nn : (0 : ℝ) ≤ (C₁ : ℝ) := Nat.cast_nonneg C₁; nlinarith
      have hr : (rounds + 1 : ℕ) = (rounds : ℝ) + 1 := by push_cast; rfl
      have hr_nn : (0 : ℝ) ≤ (rounds : ℝ) := Nat.cast_nonneg _
      have hper : (C₁ : ℝ) * (2 * polyBound Ks maxLen + 1) + 18 * (maxLen : ℝ) + 28 ≤
          (C₁ : ℝ) * (2 * polyBound Ks maxLen + 1) + (C₂ : ℝ) * (τO + σO + 1) + 27 * (maxLen : ℝ) + 42 := by
        have hm0 : (0 : ℝ) ≤ (maxLen : ℝ) := Nat.cast_nonneg _
        linarith
      have hpos_per : 0 ≤ (C₁ : ℝ) * (2 * polyBound Ks maxLen + 1) + (C₂ : ℝ) * (τO + σO + 1) + 27 * (maxLen : ℝ) + 42 := by
        have hm0 : (0 : ℝ) ≤ (maxLen : ℝ) := Nat.cast_nonneg _
        positivity
      nlinarith
    · have hr1 : 1 ≤ rounds := by
        cases rounds with
        | zero => simp at hprev
        | succ _ => omega
      let pw := pairWord st ans
      have hpw_pb : polyBound Ks pw.length ≤ polyBound Ks maxLen := polyBound_mono Ks pw.length maxLen hin_len
      have hMs_run := hMs pw
      rw [hst] at hMs_run
      obtain ⟨n1, B1, final1, ht1, hh1, ho1, hother1, hpos1, hn1, hB1, hbound1⟩ :=
        hR₁ pw (false :: pairWord st' q) (polyBound Ks pw.length) (polyBound Ks pw.length)
          (polyBound_nonneg Ks pw.length) (polyBound_nonneg Ks pw.length) hMs_run
      obtain ⟨n2, B2, final2, ht2, hh2, ho2, hother2, hpos2, hn2, hB2, hbound2⟩ :=
        hR₂ q ans' τO σO hτO hσO hO
      have hB1_le : B1 ≤ B_env := by
        have h1 : (B1 : ℝ) ≤ ((C₁ * (Nat.ceil (polyBound Ks maxLen) + 1) : ℕ) : ℝ) := by
          push_cast; nlinarith [Nat.le_ceil (polyBound Ks maxLen)]
        exact Nat.le_trans (by exact_mod_cast h1) (by omega)
      have hB2_le : B2 ≤ B_env := by
        have h2 : (B2 : ℝ) ≤ ((C₂ * (Nat.ceil σO + 1) : ℕ) : ℝ) := by
          push_cast; nlinarith [Nat.le_ceil σO]
        exact Nat.le_trans (by exact_mod_cast h2) (by omega)
      obtain ⟨t1, p1, l1, u1, n_step, htr1, hn_step, hinv1⟩ :=
        lPhase_round_cont R₁ R₂ st ans st' q ans' n1 B1 n2 B2 maxLen final1 final2
          ht1 hh1 ho1 hother1 hpos1 hbound1 ht2 hh2 ho2 hother2 hpos2 hbound2
          hin_len hmid_len hans'_len t p l u B_env hB1_le hB2_le (by omega) hinv
      obtain ⟨t2, p2, l2, u2, n_rest, htr2, hn_rest, ht2St, henv2⟩ :=
        ih st' ans' outW t1 p1 l1 u1 hr1 hprev hinv1
      refine ⟨t2, p2, l2, u2, n_step + n_rest, trace_trans htr1 htr2, ?_, ht2St, henv2⟩
      have hn_s : (n_step : ℝ) ≤ (n1 : ℝ) + (n2 : ℝ) + 27 * (maxLen : ℝ) + 42 := by exact_mod_cast hn_step
      have hn1' : (n1 : ℝ) ≤ (C₁ : ℝ) * (2 * polyBound Ks maxLen + 1) := by have hC1_nn : (0 : ℝ) ≤ (C₁ : ℝ) := Nat.cast_nonneg C₁; nlinarith
      push_cast
      linarith

end Phases

end LoopBlock

end DetDLP.M89OracleLoop

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP.M89OracleLoop

private theorem loop_time_arith (Ks C₁ C₂ K maxLen : ℕ) (τO σO : ℝ)
    (hτO : 0 ≤ τO) (hσO : 0 ≤ σO)
    (hK_Ks : Ks ≤ K) (hK_1 : 1 ≤ K)
    (hK_C1 : 2 * C₁ * Ks + C₁ + 42 ≤ K) (hK_C2 : C₂ ≤ K) :
    (C₁ : ℝ) * (2 * polyBound Ks maxLen + 1) + (C₂ : ℝ) * (τO + σO + 1) + 27 * (maxLen : ℝ) + 42 ≤
      polyBound K maxLen + (K : ℝ) * (τO + σO + 1) := by
  let m : ℝ := (maxLen : ℝ)
  let P : ℝ := (m + 1) ^ K
  have hm_nn : 0 ≤ m := Nat.cast_nonneg _
  have hm1 : 1 ≤ m + 1 := by linarith
  have hP0 : (1 : ℝ) ≤ P := one_le_pow₀ hm1
  have hP1 : m + 1 ≤ P := by
    calc
      m + 1 = (m + 1) ^ 1 := (pow_one _).symm
      _ ≤ P := pow_le_pow_right₀ hm1 hK_1
  have hpow : (m + 1) ^ Ks ≤ P := pow_le_pow_right₀ hm1 hK_Ks
  have hP_nn : 0 ≤ P := by linarith
  have hC1_nn : (0 : ℝ) ≤ (C₁ : ℝ) := Nat.cast_nonneg _
  have hKs_nn : (0 : ℝ) ≤ (Ks : ℝ) := Nat.cast_nonneg _
  have h1 : 2 * polyBound Ks maxLen + 1 ≤ 2 * ((Ks : ℝ) * P) + P := by
    simp only [polyBound]
    have hpow' : (Ks : ℝ) * (m + 1) ^ Ks ≤ (Ks : ℝ) * P := mul_le_mul_of_nonneg_left hpow hKs_nn
    linarith
  have h2 : (C₁ : ℝ) * (2 * polyBound Ks maxLen + 1) ≤ (2 * (C₁ : ℝ) * (Ks : ℝ) + (C₁ : ℝ)) * P := by
    calc
      (C₁ : ℝ) * (2 * polyBound Ks maxLen + 1)
        ≤ (C₁ : ℝ) * (2 * ((Ks : ℝ) * P) + P) := mul_le_mul_of_nonneg_left h1 hC1_nn
      _ = (2 * (C₁ : ℝ) * (Ks : ℝ) + (C₁ : ℝ)) * P := by ring
  have h3 : 27 * m + 42 ≤ 42 * P := by linarith
  have hK_C1r : 2 * (C₁ : ℝ) * (Ks : ℝ) + (C₁ : ℝ) + 42 ≤ (K : ℝ) := by exact_mod_cast hK_C1
  have hpart1 : (C₁ : ℝ) * (2 * polyBound Ks maxLen + 1) + 27 * m + 42 ≤ polyBound K maxLen := by
    calc
      (C₁ : ℝ) * (2 * polyBound Ks maxLen + 1) + 27 * m + 42
        ≤ (2 * (C₁ : ℝ) * (Ks : ℝ) + (C₁ : ℝ)) * P + 42 * P := by linarith
      _ = (2 * (C₁ : ℝ) * (Ks : ℝ) + (C₁ : ℝ) + 42) * P := by ring
      _ ≤ (K : ℝ) * P := mul_le_mul_of_nonneg_right hK_C1r hP_nn
      _ = polyBound K maxLen := by simp [polyBound, P, m]
  have hK_C2r : (C₂ : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_C2
  have hpart2 : (C₂ : ℝ) * (τO + σO + 1) ≤ (K : ℝ) * (τO + σO + 1) :=
    mul_le_mul_of_nonneg_right hK_C2r (by linarith)
  linarith

private theorem loop_space_arith (Ks C₁ C₂ T_tot K maxLen : ℕ) (σO : ℝ)
    (hσO : 0 ≤ σO) (hK_Ks : Ks ≤ K) (hK_1 : 1 ≤ K)
    (hK_1st : 2 * T_tot * C₁ * Ks + 4 * T_tot * C₁ + 11 * T_tot ≤ K)
    (hK_2nd : 4 * T_tot * C₂ ≤ K) :
    let B_env := C₁ * (Nat.ceil (polyBound Ks maxLen) + 1) + C₂ * (Nat.ceil σO + 1) + maxLen + 4
    (T_tot : ℝ) * (2 * (B_env : ℝ) + 1) ≤ polyBound K maxLen + (K : ℝ) * (σO + 1) := by
  intro B_env
  let m : ℝ := (maxLen : ℝ)
  let P : ℝ := (m + 1) ^ K
  have hm_nn : 0 ≤ m := Nat.cast_nonneg _
  have hm1 : 1 ≤ m + 1 := by linarith
  have hP0 : (1 : ℝ) ≤ P := one_le_pow₀ hm1
  have hP1 : m + 1 ≤ P := by
    calc
      m + 1 = (m + 1) ^ 1 := (pow_one _).symm
      _ ≤ P := pow_le_pow_right₀ hm1 hK_1
  have hpow : (m + 1) ^ Ks ≤ P := pow_le_pow_right₀ hm1 hK_Ks
  have hP_nn : 0 ≤ P := by linarith
  have hT_nn : (0 : ℝ) ≤ (T_tot : ℝ) := Nat.cast_nonneg _
  have hC1_nn : (0 : ℝ) ≤ (C₁ : ℝ) := Nat.cast_nonneg _
  have hC2_nn : (0 : ℝ) ≤ (C₂ : ℝ) := Nat.cast_nonneg _
  have hKs_nn : (0 : ℝ) ≤ (Ks : ℝ) := Nat.cast_nonneg _
  have hpb_nn : 0 ≤ polyBound Ks maxLen := M89OracleLoop.polyBound_nonneg Ks maxLen
  have hceil_pb : (Nat.ceil (polyBound Ks maxLen) : ℝ) < polyBound Ks maxLen + 1 :=
    Nat.ceil_lt_add_one hpb_nn
  have hceil_sig : (Nat.ceil σO : ℝ) < σO + 1 := Nat.ceil_lt_add_one hσO
  have hB_cast : (B_env : ℝ) = (C₁ : ℝ) * ((Nat.ceil (polyBound Ks maxLen) : ℝ) + 1) +
      (C₂ : ℝ) * ((Nat.ceil σO : ℝ) + 1) + m + 4 := by
    dsimp [B_env]; push_cast; ring
  have h1c : (C₁ : ℝ) * ((Nat.ceil (polyBound Ks maxLen) : ℝ) + 1) ≤ (C₁ : ℝ) * (polyBound Ks maxLen + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hC1_nn
  have h2c : (C₂ : ℝ) * ((Nat.ceil σO : ℝ) + 1) ≤ (C₂ : ℝ) * (σO + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hC2_nn
  have hB_ub : 2 * (B_env : ℝ) + 1 ≤ (2 * ((C₁ : ℝ) * (polyBound Ks maxLen + 2) + m) + 9) +
      2 * (C₂ : ℝ) * (σO + 2) := by linarith
  have hTB_ub : (T_tot : ℝ) * (2 * (B_env : ℝ) + 1) ≤
      (T_tot : ℝ) * (2 * ((C₁ : ℝ) * (polyBound Ks maxLen + 2) + m) + 9) +
      (T_tot : ℝ) * (2 * (C₂ : ℝ) * (σO + 2)) := by
    have := mul_le_mul_of_nonneg_left hB_ub hT_nn
    linarith
  have hpb_P : polyBound Ks maxLen + 2 ≤ (Ks : ℝ) * P + 2 * P := by
    simp only [polyBound]
    have hpow' : (Ks : ℝ) * (m + 1) ^ Ks ≤ (Ks : ℝ) * P := mul_le_mul_of_nonneg_left hpow hKs_nn
    linarith
  have hC1_P : 2 * ((C₁ : ℝ) * (polyBound Ks maxLen + 2)) ≤ (2 * (C₁ : ℝ) * (Ks : ℝ) + 4 * (C₁ : ℝ)) * P := by
    calc
      2 * ((C₁ : ℝ) * (polyBound Ks maxLen + 2))
        ≤ 2 * ((C₁ : ℝ) * ((Ks : ℝ) * P + 2 * P)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpb_P hC1_nn) (by norm_num)
      _ = (2 * (C₁ : ℝ) * (Ks : ℝ) + 4 * (C₁ : ℝ)) * P := by ring
  have h2m9 : 2 * m + 9 ≤ 11 * P := by linarith
  have hinner : 2 * ((C₁ : ℝ) * (polyBound Ks maxLen + 2) + m) + 9 ≤
      (2 * (C₁ : ℝ) * (Ks : ℝ) + 4 * (C₁ : ℝ) + 11) * P := by
    calc
      2 * ((C₁ : ℝ) * (polyBound Ks maxLen + 2) + m) + 9
        ≤ (2 * (C₁ : ℝ) * (Ks : ℝ) + 4 * (C₁ : ℝ)) * P + 11 * P := by linarith
      _ = (2 * (C₁ : ℝ) * (Ks : ℝ) + 4 * (C₁ : ℝ) + 11) * P := by ring
  have hK_1str : 2 * (T_tot : ℝ) * (C₁ : ℝ) * (Ks : ℝ) + 4 * (T_tot : ℝ) * (C₁ : ℝ) + 11 * (T_tot : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hK_1st
  have hpart1 : (T_tot : ℝ) * (2 * ((C₁ : ℝ) * (polyBound Ks maxLen + 2) + m) + 9) ≤ polyBound K maxLen := by
    calc
      (T_tot : ℝ) * (2 * ((C₁ : ℝ) * (polyBound Ks maxLen + 2) + m) + 9)
        ≤ (T_tot : ℝ) * ((2 * (C₁ : ℝ) * (Ks : ℝ) + 4 * (C₁ : ℝ) + 11) * P) :=
          mul_le_mul_of_nonneg_left hinner hT_nn
      _ = (2 * (T_tot : ℝ) * (C₁ : ℝ) * (Ks : ℝ) + 4 * (T_tot : ℝ) * (C₁ : ℝ) + 11 * (T_tot : ℝ)) * P := by ring
      _ ≤ (K : ℝ) * P := mul_le_mul_of_nonneg_right hK_1str hP_nn
      _ = polyBound K maxLen := by simp [polyBound, P, m]
  have hK_2ndr : 4 * (T_tot : ℝ) * (C₂ : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_2nd
  have hsig_2 : σO + 2 ≤ 2 * (σO + 1) := by linarith
  have hTC2_nn : 0 ≤ 2 * (T_tot : ℝ) * (C₂ : ℝ) := by positivity
  have hpart2 : (T_tot : ℝ) * (2 * (C₂ : ℝ) * (σO + 2)) ≤ (K : ℝ) * (σO + 1) := by
    calc
      (T_tot : ℝ) * (2 * (C₂ : ℝ) * (σO + 2))
        = (2 * (T_tot : ℝ) * (C₂ : ℝ)) * (σO + 2) := by ring
      _ ≤ (2 * (T_tot : ℝ) * (C₂ : ℝ)) * (2 * (σO + 1)) := mul_le_mul_of_nonneg_left hsig_2 hTC2_nn
      _ = (4 * (T_tot : ℝ) * (C₂ : ℝ)) * (σO + 1) := by ring
      _ ≤ (K : ℝ) * (σO + 1) := mul_le_mul_of_nonneg_right hK_2ndr (by linarith)
  linarith

theorem m89_polyT_oracle_loop_proved
    (step : List Bool → List Bool) (hstep : Groundwork.PolyT step)
    (O : PrimitiveMachine) (outO : Fin O.tapeCount) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      1 ≤ K ∧
      ∀ (τO σO : ℝ), 0 ≤ τO → 0 ≤ σO →
        let pairWord : List Bool → List Bool → List Bool := fun x y =>
          x.flatMap (fun b => [true, b]) ++ [false] ++ y
        let loopRuns : ℕ → List Bool → List Bool → List Bool → ℕ → Prop :=
          Nat.rec (motive := fun _ => List Bool → List Bool → List Bool → ℕ → Prop)
            (fun _ _ _ _ => False)
            (fun _ prev st ans outW maxLen =>
              (step (pairWord st ans) = true :: outW ∧
                (pairWord st ans).length ≤ maxLen ∧ outW.length ≤ maxLen) ∨
              (∃ st' q ans',
                step (pairWord st ans) = false :: pairWord st' q ∧
                (pairWord st ans).length ≤ maxLen ∧
                (pairWord st' q).length ≤ maxLen ∧
                ans'.length ≤ maxLen ∧
                RunsWithin O outO q ans' τO σO ∧
                prev st' ans' outW maxLen))
        ∀ (rounds maxLen : ℕ) (input output : List Bool),
          1 ≤ rounds →
          loopRuns rounds input [] output maxLen →
          RunsWithin M out input output
            ((rounds : ℝ) * (polyBound K maxLen + (K : ℝ) * (τO + σO + 1)))
            (polyBound K maxLen + (K : ℝ) * (σO + 1)) := by
  obtain ⟨Ms, outs, Ks, hMs⟩ := DetDLP.PolyTBridge.polyT_listBool_runsWithin step hstep
  obtain ⟨R₁, C₁, hC₁, hR₁⟩ := DetDLP.m89_resettable_machine Ms outs
  obtain ⟨R₂, C₂, hC₂, hR₂⟩ := DetDLP.m89_resettable_machine O outO
  let M := loopMachine R₁ R₂
  let out : Fin M.tapeCount := Fintype.equivFin (LTape R₁.tapeCount R₂.tapeCount) tSt
  let T_tot := M.tapeCount
  let K := max Ks 1 + 12 * T_tot * (C₁ + C₂ + 1) + 2 * T_tot * C₁ * Ks + 100
  have hT_ge2 : 2 ≤ T_tot := by
    change 2 ≤ Fintype.card (LTape R₁.tapeCount R₂.tapeCount)
    simp [LTape]
  have hK_def : K = max Ks 1 + (12 * T_tot * C₁ + 12 * T_tot * C₂ + 12 * T_tot) +
      2 * T_tot * C₁ * Ks + 100 := by dsimp [K]; ring
  have hC1_le : C₁ ≤ 12 * T_tot * C₁ := by
    calc
      C₁ = 1 * C₁ := (one_mul _).symm
      _ ≤ (12 * T_tot) * C₁ := Nat.mul_le_mul_right C₁ (by omega)
      _ = 12 * T_tot * C₁ := by ring
  have hC2_le : C₂ ≤ 12 * T_tot * C₂ := by
    calc
      C₂ = 1 * C₂ := (one_mul _).symm
      _ ≤ (12 * T_tot) * C₂ := Nat.mul_le_mul_right C₂ (by omega)
      _ = 12 * T_tot * C₂ := by ring
  have h4C1_le : 4 * T_tot * C₁ ≤ 12 * T_tot * C₁ :=
    Nat.mul_le_mul_right C₁ (by omega)
  have h4C2_le : 4 * T_tot * C₂ ≤ 12 * T_tot * C₂ :=
    Nat.mul_le_mul_right C₂ (by omega)
  have hKsC1_le : 2 * C₁ * Ks ≤ 2 * T_tot * C₁ * Ks := by
    calc
      2 * C₁ * Ks = 1 * (2 * C₁ * Ks) := (one_mul _).symm
      _ ≤ T_tot * (2 * C₁ * Ks) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * T_tot * C₁ * Ks := by ring
  have hK_Ks : Ks ≤ K := by omega
  have hK_1 : 1 ≤ K := by omega
  have hK_C1 : 2 * C₁ * Ks + C₁ + 42 ≤ K := by omega
  have hK_C2 : C₂ ≤ K := by omega
  have hK_1st : 2 * T_tot * C₁ * Ks + 4 * T_tot * C₁ + 11 * T_tot ≤ K := by omega
  have hK_2nd : 4 * T_tot * C₂ ≤ K := by omega
  refine ⟨M, out, K, hK_1, ?_⟩
  intro τO σO hτO hσO pairWord loopRuns rounds maxLen input output hrounds hrun
  rw [DetDLP.MachineComposition.runsWithin_iff_final_space]
  let B_env := C₁ * (Nat.ceil (polyBound Ks maxLen) + 1) + C₂ * (Nat.ceil σO + 1) + maxLen + 4
  have hlen_in : input.length ≤ maxLen := by
    have hin_pw : input.length ≤ (pairWord input []).length := by
      dsimp [pairWord]; rw [List.length_append, List.length_append, M89OracleLoop.list_flatMap_pair_length]; omega
    cases rounds with
    | zero => omega
    | succ r =>
      rcases hrun with ⟨_, hm, _⟩ | ⟨_, _, _, _, hm, _⟩ <;> omega
  let t0 : M89OracleLoop.LCfg R₁.tapeCount R₂.tapeCount :=
    fun r => if r = tSt then Turing.Tape.mk₁ (input.map some) else Turing.Tape.mk₁ []
  let p0 : M89OracleLoop.LPos R₁.tapeCount R₂.tapeCount := fun _ => 0
  let l0 : M89OracleLoop.LPos R₁.tapeCount R₂.tapeCount := fun _ => 0
  let u0 : M89OracleLoop.LPos R₁.tapeCount R₂.tapeCount :=
    fun r => if r = tSt then Int.ofNat (input.length - 1) else 0
  have hinit_eq : locatedInit M input =
      M89OracleLoop.cCfg (M89OracleLoop.loopOps R₁ R₂) M89OracleLoop.qEncStCheck tSt
        (.inr M89OracleLoop.qEncStCheck) t0 p0 l0 u0 := by
    apply M89OracleLoop.loc_ext
    · rfl
    · intro i
      obtain ⟨r, rfl⟩ := (Fintype.equivFin (LTape R₁.tapeCount R₂.tapeCount)).surjective i
      simp only [locatedInit, PrimitiveMachine.init, M89OracleLoop.cCfg, M89OracleLoop.packTapes_apply,
        M89OracleLoop.cMachine, M89OracleLoop.loopMachine, M, t0]
      by_cases hr : r = tSt
      · subst hr; simp
      · have hne := (Fintype.equivFin (LTape R₁.tapeCount R₂.tapeCount)).injective.ne hr
        simp [hr, hne]
    · intro i
      obtain ⟨r, rfl⟩ := (Fintype.equivFin (LTape R₁.tapeCount R₂.tapeCount)).surjective i
      simp [locatedInit, M89OracleLoop.cCfg, p0]
    · intro i
      obtain ⟨r, rfl⟩ := (Fintype.equivFin (LTape R₁.tapeCount R₂.tapeCount)).surjective i
      simp [locatedInit, M89OracleLoop.cCfg, l0]
    · intro i
      obtain ⟨r, rfl⟩ := (Fintype.equivFin (LTape R₁.tapeCount R₂.tapeCount)).surjective i
      simp only [locatedInit, M89OracleLoop.cCfg, M89OracleLoop.packTapes_apply,
        M89OracleLoop.cMachine, M89OracleLoop.loopMachine, M, u0]
      by_cases hr : r = tSt
      · subst hr; simp
      · have hne := (Fintype.equivFin (LTape R₁.tapeCount R₂.tapeCount)).injective.ne hr
        simp [hr, hne]
  have hB_max : maxLen + 4 ≤ B_env := by dsimp [B_env]; omega
  have hinv0 : M89OracleLoop.LoopInv t0 p0 l0 u0 (-(B_env : ℤ)) (B_env : ℤ)
      R₁.inputTape R₂.inputTape input [] := by
    refine ⟨by simp [t0], by simp [p0], by simp [t0], by simp [p0],
      fun j => ⟨by simp [t0], by simp [p0]⟩,
      fun j => ⟨by simp [t0], by simp [p0]⟩,
      fun r => ?_, fun r => ?_⟩
    · by_cases hr : r = tSt
      · subst r; simp [l0, p0, u0]
      · simp [l0, p0, u0, hr]
    · by_cases hr : r = tSt
      · subst r; dsimp only [l0, u0]; simp; omega
      · simp [l0, u0, hr]
  obtain ⟨t1, p1, l1, u1, n, htr, hn_le, ht1St, henv1⟩ :=
    M89OracleLoop.lPhase_rounds step Ms outs Ks hMs O outO R₁ C₁ hC₁ hR₁ R₂ C₂ hC₂ hR₂
      τO σO hτO hσO maxLen rounds input [] output t0 p0 l0 u0 hrounds hrun hinv0
  rw [← hinit_eq] at htr
  let final := M89OracleLoop.cCfg (M89OracleLoop.loopOps R₁ R₂) M89OracleLoop.qEncStCheck tSt
    (.inl true) t1 p1 l1 u1
  refine ⟨n, final, htr, ⟨true, rfl⟩, ?_, ?_, ?_⟩
  · simpa [final, out, M89OracleLoop.cCfg, M89OracleLoop.packTapes_apply] using ht1St
  · have hper := loop_time_arith Ks C₁ C₂ K maxLen τO σO hτO hσO hK_Ks hK_1 hK_C1 hK_C2
    exact le_trans hn_le (mul_le_mul_of_nonneg_left hper (Nat.cast_nonneg _))
  · have hvis : visitedSpace final ≤ T_tot * (2 * B_env + 1) := by
      unfold visitedSpace
      have hterm : ∀ i : Fin M.tapeCount, (final.upper i - final.lower i + 1).toNat ≤ 2 * B_env + 1 := by
        intro i
        obtain ⟨r, rfl⟩ := (Fintype.equivFin (LTape R₁.tapeCount R₂.tapeCount)).surjective i
        have hr := henv1 r
        have hlo : final.lower (Fintype.equivFin _ r) = l1 r := by
          simp [final, M89OracleLoop.cCfg, M89OracleLoop.packTapes_apply]
        have hhi : final.upper (Fintype.equivFin _ r) = u1 r := by
          simp [final, M89OracleLoop.cCfg, M89OracleLoop.packTapes_apply]
        rw [hlo, hhi]
        omega
      calc
        ∑ i : Fin M.tapeCount, (final.upper i - final.lower i + 1).toNat
          ≤ ∑ _i : Fin M.tapeCount, (2 * B_env + 1) := Finset.sum_le_sum (fun i _ => hterm i)
        _ = M.tapeCount * (2 * B_env + 1) := by simp
    have hvis_r : (visitedSpace final : ℝ) ≤ (T_tot : ℝ) * (2 * (B_env : ℝ) + 1) := by exact_mod_cast hvis
    exact le_trans hvis_r (loop_space_arith Ks C₁ C₂ T_tot K maxLen σO hσO hK_Ks hK_1 hK_1st hK_2nd)

end DetDLP

theorem solution
    (step : List Bool → List Bool) (hstep : Groundwork.PolyT step)
    (O : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine) (outO : Fin O.tapeCount) :
    ∃ (M : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      1 ≤ K ∧
      ∀ (τO σO : ℝ), 0 ≤ τO → 0 ≤ σO →
        let pairWord : List Bool → List Bool → List Bool := fun x y =>
          x.flatMap (fun b => [true, b]) ++ [false] ++ y
        let loopRuns : ℕ → List Bool → List Bool → List Bool → ℕ → Prop :=
          Nat.rec (motive := fun _ => List Bool → List Bool → List Bool → ℕ → Prop)
            (fun _ _ _ _ => False)
            (fun _ prev st ans outW maxLen =>
              (step (pairWord st ans) = true :: outW ∧
                (pairWord st ans).length ≤ maxLen ∧ outW.length ≤ maxLen) ∨
              (∃ st' q ans',
                step (pairWord st ans) = false :: pairWord st' q ∧
                (pairWord st ans).length ≤ maxLen ∧
                (pairWord st' q).length ≤ maxLen ∧
                ans'.length ≤ maxLen ∧
                DetDLP.RunsWithin O outO q ans' τO σO ∧
                prev st' ans' outW maxLen))
        ∀ (rounds maxLen : ℕ) (input output : List Bool),
          1 ≤ rounds →
          loopRuns rounds input [] output maxLen →
          DetDLP.RunsWithin M out input output
            ((rounds : ℝ) * (DetDLP.polyBound K maxLen + (K : ℝ) * (τO + σO + 1)))
            (DetDLP.polyBound K maxLen + (K : ℝ) * (σO + 1)) :=
  DetDLP.m89_polyT_oracle_loop_proved step hstep O outO
