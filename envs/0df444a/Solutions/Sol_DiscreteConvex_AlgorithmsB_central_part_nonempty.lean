-- Prove2me | solution 1 for DiscreteConvex.AlgorithmsB.central_part_nonempty
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:01:12.300061+00:00
-- url     : https://prove2.me/submissions/7e8f010b-5a5d-46c1-a720-177382c5c9bd

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_AlgorithmsB_BCirc

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.AlgorithmsB

namespace CentralCex

/-- `B = {(1,0), (0,1)}` (coordinates `true`, `false`): a bounded M-convex set in dimension 2. -/
def B : Set (Bool → ℤ) := {x | x true + x false = 1 ∧ 0 ≤ x true ∧ x true ≤ 1}

theorem B_exc : ExchangeAxiomB B := by
  rintro x ⟨hx1, hx2, hx3⟩ y ⟨hy1, hy2, hy3⟩ u hu
  simp only [SuppPos, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  refine ⟨!u, ?_, ?_, ?_⟩
  · simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and]
    cases u <;> simp only [Bool.not_true, Bool.not_false] <;> omega
  · cases u <;> refine ⟨?_, ?_, ?_⟩ <;> (try simp) <;> omega
  · cases u <;> refine ⟨?_, ?_, ?_⟩ <;> (try simp) <;> omega

theorem image_eq (v : Bool) : (fun y : Bool → ℤ => y v) '' B = Set.Icc 0 1 := by
  ext k
  simp only [Set.mem_image, Set.mem_Icc, B, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, ⟨h1, h2, h3⟩, rfl⟩
    cases v <;> (try simp) <;> omega
  · rintro ⟨hk0, hk1⟩
    cases v
    · exact ⟨fun b => if b then 1 - k else k, by simp; omega, by simp⟩
    · exact ⟨fun b => if b then k else 1 - k, by simp; omega, by simp⟩

theorem LB_eq (v : Bool) : LB B v = 0 := by
  unfold LB; rw [image_eq]; exact csInf_Icc (by norm_num)

theorem UB_eq (v : Bool) : UB B v = 1 := by
  unfold UB; rw [image_eq]; exact csSup_Icc (by norm_num)

theorem LBC (v : Bool) : LBCirc B v = 1 / 2 := by
  unfold LBCirc; rw [LB_eq, UB_eq]; norm_num

theorem UBC (v : Bool) : UBCirc B v = 1 / 2 := by
  unfold UBCirc; rw [LB_eq, UB_eq]; norm_num

/-- No integer vector meets the central bounds `1/2 ≤ y(v) ≤ 1/2`. -/
theorem no_central (y : Bool → ℤ) (v : Bool) :
    ¬ (LBCirc B v ≤ (y v : ℚ) ∧ (y v : ℚ) ≤ UBCirc B v) := by
  rintro ⟨h1, h2⟩
  rw [LBC] at h1; rw [UBC] at h2
  have h : (y v : ℚ) = 1 / 2 := le_antisymm h2 h1
  have : (2 * y v : ℚ) = 1 := by rw [h]; norm_num
  have : (2 * y v : ℤ) = 1 := by exact_mod_cast this
  omega

end CentralCex

open CentralCex in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (B : Set (V → ℤ)) (hB : ExchangeAxiomB B) (hBne : B.Nonempty)
    (hBbdd : ∃ N : ℤ, ∀ y ∈ B, ∀ v, -N ≤ y v ∧ y v ≤ N),
    (BCirc B).Nonempty) := by
  intro h
  obtain ⟨y, -, hy⟩ := h B B_exc ⟨fun b => if b then 1 else 0, by simp [B]⟩
    ⟨1, fun y ⟨h1, h2, h3⟩ v => by cases v <;> (try simp) <;> omega⟩
  exact no_central y true (hy true)

#print axioms solution
