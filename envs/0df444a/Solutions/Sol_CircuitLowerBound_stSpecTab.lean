-- Prove2me | solution 1 for CircuitLowerBound.stSpecTab
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:29:36.994175+00:00
-- url     : https://prove2.me/submissions/5464fe45-e20e-49dc-958b-de1982e1be54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Table
set_option autoImplicit false
section
section
open CircuitLowerBound
open Tab Turing

namespace CircuitLowerBound.Tab

open ENP Turing

section generic

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- A statement with d stack operations makes a stack longer by at most d. -/
theorem length_stepAux_le (q : TM2.Stmt Γ Λ σ) :
    ∀ (v : σ) (A : ∀ k, List (Γ k)) (k : K),
      ((TM2.stepAux q v A).stk k).length ≤ (A k).length + ops q := by
  induction q with
  | push k f q ih =>
    intro v A k'
    simp only [TM2.stepAux]
    refine (ih _ _ k').trans ?_
    by_cases e : k' = k
    · subst e; simp [ops]; omega
    · simp [Function.update_of_ne e, ops]
  | peek k f q ih =>
    intro v A k'; simp only [TM2.stepAux]; exact (ih _ _ k').trans (by simp [ops])
  | pop k f q ih =>
    intro v A k'
    simp only [TM2.stepAux]
    refine (ih _ _ k').trans ?_
    by_cases e : k' = k
    · subst e; simp [ops]; omega
    · simp [Function.update_of_ne e, ops]
  | load a q ih => intro v A k'; simp only [TM2.stepAux]; exact ih _ _ k'
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v A k'
    simp only [TM2.stepAux]
    cases f v
    · exact (ih₂ v A k').trans (by simp [ops])
    · exact (ih₁ v A k').trans (by simp [ops])
  | goto f => intro v A k'; simp [TM2.stepAux, ops]
  | halt => intro v A k'; simp [TM2.stepAux, ops]

end generic

theorem length_pref_le {α : Type} : ∀ L : List (Option α), (pref L).length ≤ L.length
  | [] => le_rfl
  | none :: L => by simp [pref]
  | some a :: L => by simpa [pref] using length_pref_le L

variable (N : TM2ComputableAux Bool Bool)

theorem tval0 (b t : ℕ) : tval b t 0 = 0 := by simp [tval]
theorem tval1 (b t : ℕ) : tval b t 1 = t := by simp [tval]
theorem tval2 (b t : ℕ) : tval b t 2 = t + 1 := by simp [tval]
theorem tval3 (b t : ℕ) : tval b t 3 = 2 ^ b := by simp [tval]
theorem qval0 (P q : ℕ) : qval P q 0 = 0 := by simp [qval]
theorem qval1 (P q : ℕ) : qval P q 1 = q := by simp [qval]
theorem qval2 (P q : ℕ) : qval P q 2 = P := by simp [qval]

theorem holdsC_taut (α : Atom N → ℕ → ℕ → Bool) (b Q P : ℕ) : HoldsC α b Q P taut := by
  intro t _ q _
  simp only [taut, holdsY]
  cases α .u (tval b t 0) (qval P q 0 + 0) <;> simp

theorem mem_en {ι : Type} [Finite ι] (i : ι) : i ∈ en ι := by simp [en]

theorem forall_fam {ι : Type} [Finite ι] {f : ι → YCl N} {p : YCl N → Prop} :
    (∀ c ∈ fam f, p c) ↔ ∀ i, p (f i) := by
  simp [fam, mem_en]

theorem forall_flatten {β : Type} {p : β → Prop} {Ls : List (List β)} :
    (∀ c ∈ Ls.flatten, p c) ↔ ∀ l ∈ Ls, ∀ c ∈ l, p c := by
  simp only [List.mem_flatten]
  exact ⟨fun h l hl c hc => h c ⟨l, hl, hc⟩, fun h c ⟨l, hl, hc⟩ => h l hl c hc⟩

theorem ops_le_dep (l : N.tm.Λ) : ops (N.tm.m l) ≤ dep N :=
  le_trans (Finset.le_sup (f := fun l : N.tm.Λ => ops (N.tm.m l)) (Finset.mem_univ l))
    (le_max_right _ _)

theorem one_le_dep : 1 ≤ dep N := le_max_left _ _

/-- The new top of a stack has at most 2d symbols. -/
theorem length_nxt_le (γ : Case N) (k : N.tm.K) : ((nxt N γ).stk k).length ≤ 2 * dep N := by
  obtain ⟨l, v, w⟩ := γ
  have h1 : (pref (List.ofFn (w k))).length ≤ dep N := (length_pref_le _).trans (by simp)
  cases l with
  | none => simp only [nxt]; omega
  | some l =>
    simp only [nxt]
    have := length_stepAux_le (N.tm.m l) v (fun k => pref (List.ofFn (w k))) k
    have := ops_le_dep N l
    omega

variable [Finite (Case N)] [∀ k, Finite (N.tm.Γ k)]
variable {N}

theorem bool_imp {x : Bool} {p : Prop} : (x = false ∨ p ∨ p) ↔ (x = true → p) := by
  cases x <;> simp

theorem bool_dec {y : Bool} {p : Prop} [Decidable p] : y = decide p ↔ (y = true ↔ p) := by
  by_cases hp : p <;> cases y <;> simp [hp]

theorem bool_copy {x y z : Bool} :
    ((x = false ∨ y = false ∨ z = true) ∧ (x = false ∨ y = true ∨ z = false)) ↔
      (x = true → y = z) := by
  cases x <;> cases y <;> cases z <;> simp

theorem or_self3 {p : Prop} : (p ∨ p ∨ p) ↔ p := by tauto

/-- If all shifts of the clauses of the table hold, the conditions hold. -/
theorem spec_of_table {α : Atom N → ℕ → ℕ → Bool} {b Q P : ℕ}
    (H : ∀ c ∈ table N, HoldsC α b Q P c) : Spec N α b Q P := by
  classical
  have hQ : 0 < 2 ^ Q := by positivity
  have hb : 0 < 2 ^ b := by positivity
  simp only [table, forall_flatten, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    implies_true, and_true, forall_fam] at H
  revert H
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
      a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28⟩
    simp only [HoldsC, holdsY, c1, c2, tval0, tval1, tval2, tval3, qval0, qval1, qval2,
      Nat.zero_add, Nat.add_zero, bool_imp, bool_dec, or_self3]
      at a1 a2 a3 a4 a5 a6 a7 a8 a9 a11 a12 a13 a14 a16 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27
    exact
      { preTop := fun t ht => a1 t ht 0 hQ
        preBot := fun t ht => a2 t ht 0 hQ
        preStep := fun t ht i => a3 i t ht 0 hQ
        csLab := fun t ht γ => a4 γ t ht 0 hQ
        csVar := fun t ht γ => a5 γ t ht 0 hQ
        csCell := fun t ht γ k j => a6 (γ, k, j) t ht 0 hQ
        nxLab := fun t ht γ x => a7 (γ, x) t ht 0 hQ
        nxVar := fun t ht γ x => a8 (γ, x) t ht 0 hQ
        nxLen := fun t ht γ k n => a9 (γ, k, n) t ht 0 hQ
        nxCell := fun t ht γ k x j hj => by
          have hj2 : j < 2 * dep N := lt_of_lt_of_le hj (length_nxt_le N γ k)
          have := a10 (γ, ⟨k, x⟩, ⟨j, hj2⟩)
          rw [if_pos hj] at this
          simpa only [HoldsC, holdsY, c2, tval1, tval2, qval0, Nat.zero_add, bool_imp,
            bool_dec] using this t ht 0 hQ
        copy := fun t ht q hq k n x =>
          bool_copy.1 ⟨a11 (⟨k, x⟩, n) t ht q hq, a12 (⟨k, x⟩, n) t ht q hq⟩
        iLab := fun x => a13 x 0 hb 0 hQ
        iVar := fun x => a14 x 0 hb 0 hQ
        iCell := fun q hq k hk x => by
          have := a15 ⟨k, x⟩
          rw [if_pos hk] at this
          simpa only [HoldsC, holdsY, c1, tval0, qval1, Nat.add_zero, or_self3, bool_dec]
            using this 0 hb q hq
        iSome := fun q hq => a16 0 hb q hq
        iMost := fun q hq x x' hne => by
          have := a17 (x, x')
          rw [if_pos hne] at this
          have := this 0 hb q hq
          simp only [holdsY, c2, tval0, qval1, Nat.add_zero] at this
          tauto
        iBlank := fun q hq => a18 0 hb q hq
        uStep := fun q hq => a19 0 hb q hq
        uP := a20 0 hb 0 hQ
        uP1 := a21 0 hb 0 hQ
        uOne := fun q hq => a22 0 hb q hq
        cellP := a23 0 hb 0 hQ
        fLab := a24 0 hb 0 hQ
        fVar := a25 0 hb 0 hQ
        fOut0 := a26 0 hb 0 hQ
        fOut1 := a27 0 hb 0 hQ
        fOther := fun k hk => by
          have := a28 k
          rw [if_pos hk] at this
          simpa only [HoldsC, holdsY, c1, tval3, qval0, Nat.add_zero, or_self3]
            using this 0 hb 0 hQ }

/-- If the conditions hold, all shifts of the clauses of the table hold. -/
theorem table_of_spec {α : Atom N → ℕ → ℕ → Bool} {b Q P : ℕ}
    (h : Spec N α b Q P) : ∀ c ∈ table N, HoldsC α b Q P c := by
  classical
  simp only [table, forall_flatten, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    implies_true, and_true, forall_fam]
  · simp only [HoldsC, holdsY, c1, c2, tval0, tval1, tval2, tval3, qval0, qval1, qval2,
      Nat.zero_add, Nat.add_zero, bool_imp, bool_dec, or_self3]
    refine ⟨fun t ht _ _ => h.preTop t ht, fun t ht _ _ => h.preBot t ht,
      fun i t ht _ _ => h.preStep t ht i, fun γ t ht _ _ => h.csLab t ht γ,
      fun γ t ht _ _ => h.csVar t ht γ,
      fun p t ht _ _ => h.csCell t ht p.1 p.2.1 p.2.2,
      fun p t ht _ _ => h.nxLab t ht p.1 p.2,
      fun p t ht _ _ => h.nxVar t ht p.1 p.2,
      fun p t ht _ _ => h.nxLen t ht p.1 p.2.1 p.2.2, fun p => ?_,
      fun p t ht q hq => ?_, fun p t ht q hq => ?_,
      fun x _ _ _ _ => h.iLab x, fun x _ _ _ _ => h.iVar x, fun p => ?_,
      fun _ _ q hq => h.iSome q hq, fun p => ?_, fun _ _ q hq => h.iBlank q hq,
      fun _ _ q hq => h.uStep q hq, fun _ _ _ _ => h.uP, fun _ _ _ _ => h.uP1,
      fun _ _ q hq => h.uOne q hq, fun _ _ _ _ => h.cellP,
      fun _ _ _ _ => h.fLab, fun _ _ _ _ => h.fVar, fun _ _ _ _ => h.fOut0,
      fun _ _ _ _ => h.fOut1, fun k => ?_⟩
    · split_ifs with hj
      · intro t ht q _
        simp only [tval1, tval2, qval0, Nat.zero_add, bool_imp, bool_dec]
        exact h.nxCell t ht p.1 p.2.1.1 p.2.1.2 p.2.2 hj
      · exact holdsC_taut (N := N) α b Q P
    · exact (bool_copy.2 (h.copy t ht q hq p.1.1 p.2 p.1.2)).1
    · exact (bool_copy.2 (h.copy t ht q hq p.1.1 p.2 p.1.2)).2
    · split_ifs with hk
      · intro t _ q hq
        simp only [tval0, qval1, Nat.add_zero, or_self3, bool_dec]
        exact h.iCell q hq p.1 hk p.2
      · exact holdsC_taut (N := N) α b Q P
    · split_ifs with hne
      · intro t _ q hq
        simp only [tval0, qval1, Nat.add_zero]
        have := h.iMost q hq p.1 p.2 hne
        tauto
      · exact holdsC_taut (N := N) α b Q P
    · split_ifs with hk
      · intro t _ q _
        simp only [tval3, qval0, Nat.add_zero, or_self3]
        exact h.fOther k hk
      · exact holdsC_taut (N := N) α b Q P

/-- The numbers added to positions are at most 2d. -/
theorem table_dq : ∀ c ∈ table N,
    c.1.2.2.2.1 ≤ 2 * dep N ∧ c.2.1.2.2.2.1 ≤ 2 * dep N ∧
      c.2.2.2.2.2.1 ≤ 2 * dep N := by
  classical
  have hd := one_le_dep N
  simp only [table, forall_flatten, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    implies_true, and_true, forall_fam]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case refine_6 => intro p; have := p.2.2.isLt; simp only [c2]; omega
  case refine_10 => intro p; have := p.2.2.isLt; split_ifs <;> simp only [c2, taut] <;> omega
  case refine_11 => intro p; have := p.2.isLt; omega
  case refine_12 => intro p; have := p.2.isLt; omega
  all_goals (intros; (try split_ifs) <;> (try simp only [c1, c2, taut]) <;> omega)

/-- The number of an atom is injective. -/
theorem num_injective : Function.Injective (num (N := N)) := fun a a' h =>
  (Finite.equivFin (Atom N)).injective (Fin.ext (by simpa [num] using h))

end CircuitLowerBound.Tab

open Tab Turing

/-- The conditions are the shifts of a table. -/
theorem solution : StSpecTab := by
  intro N _ hfin
  have : ∀ k, Finite (N.tm.Γ k) := hfin
  refine ⟨codeTab N, ?_, rfl, fun b Q P => ?_⟩
  · intro c hc l hl
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    have hdq := table_dq c' hc'
    have hlam : 2 * dep N + 2 < 2 ^ lamOf N := Nat.lt_size_self _
    have hnum : ∀ a : Atom N, 1 ≤ num a ∧ num a < 2 ^ kb (codeTab N) := fun a =>
      ⟨by simp [num], lt_trans
        (by have := (Finite.equivFin (Atom N) a).isLt; simp only [num]; omega)
        (Nat.lt_size_self _)⟩
    have hl' : lam (codeTab N) = lamOf N := rfl
    simp only [lits, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact ⟨(hnum _).1, (hnum _).2, by rw [hl']; simp only [nl]; omega⟩
    · exact ⟨(hnum _).1, (hnum _).2, by rw [hl']; simp only [nl]; omega⟩
    · exact ⟨(hnum _).1, (hnum _).2, by rw [hl']; simp only [nl]; omega⟩
  · have key : ∀ (β : ℕ → ℕ → ℕ → Bool) (α : Atom N → ℕ → ℕ → Bool),
        (∀ a t q, β (num a) t q = α a t q) →
        ((∀ c ∈ tab (codeTab N), ∀ t < 2 ^ b, ∀ q < 2 ^ Q,
            ∃ l ∈ lits c, holdsT β b P t q l) ↔
          ∀ c ∈ table N, HoldsC α b Q P c) := by
      intro β α h
      simp only [tab, codeTab, List.forall_mem_map, lits, List.mem_cons, List.not_mem_nil,
        or_false, exists_eq_or_imp, exists_eq_left, holdsT, nl, h]
      rfl
    constructor
    · rintro ⟨β, hβ⟩
      exact ⟨fun a t q => β (num a) t q,
        spec_of_table ((key β _ fun _ _ _ => rfl).1 hβ)⟩
    · rintro ⟨α, hα⟩
      classical
      refine ⟨fun k t q => if h : ∃ a, num a = k then α h.choose t q else false,
        (key _ α fun a t q => ?_).2 (table_of_spec hα)⟩
      have h : ∃ a', num a' = num a := ⟨a, rfl⟩
      rw [dif_pos h, num_injective h.choose_spec]
