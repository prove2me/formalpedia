-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityB.theorem_3_10_lp_duality
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:28:07.265503+00:00
-- url     : https://prove2.me/submissions/06b3396c-87c7-4817-9bf8-79ca19b817d1

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_PrimalFeas
import Definitions.Def_DiscreteConvex_IntegralConvexityB_DualFeas

open DiscreteConvex.IntegralConvexityB

theorem solution : ¬ (∀ {V W : Type} [Fintype V] [Fintype W] (A : Matrix W V ℝ)
    (b : W → ℝ) (c : V → ℝ),
    (∀ x ∈ PrimalFeas A b, ∀ y ∈ DualFeas A c, dotProduct c x ≥ dotProduct b y) ∧
      ((PrimalFeas A b).Nonempty ∨ (DualFeas A c).Nonempty →
        sInf {v : EReal | ∃ x ∈ PrimalFeas A b, v = (dotProduct c x : ℝ)} =
            sSup {v : EReal | ∃ y ∈ DualFeas A c, v = (dotProduct b y : ℝ)} ∧
          (∀ vstar : ℝ,
            sInf {v : EReal | ∃ x ∈ PrimalFeas A b, v = (dotProduct c x : ℝ)} = (vstar : EReal) ↔
              (PrimalFeas A b).Nonempty ∧ (DualFeas A c).Nonempty) ∧
          ((PrimalFeas A b).Nonempty → (DualFeas A c).Nonempty →
            (∃ x ∈ PrimalFeas A b, ∀ x' ∈ PrimalFeas A b, dotProduct c x ≤ dotProduct c x') ∧
              (∃ y ∈ DualFeas A c, ∀ y' ∈ DualFeas A c, dotProduct b y ≥ dotProduct b y'))) ∧
      (∀ x ∈ PrimalFeas A b, ∀ y ∈ DualFeas A c,
        ((∀ x' ∈ PrimalFeas A b, dotProduct c x ≤ dotProduct c x') ∧
            ∀ y' ∈ DualFeas A c, dotProduct b y ≥ dotProduct b y') ↔
          ∀ j, x j = 0 ∨ Matrix.vecMul y A j - c j = 0)) := by
  intro h
  have hP : (PrimalFeas (0 : Matrix Unit Unit ℝ) (0 : Unit → ℝ)).Nonempty :=
    ⟨0, by simp [PrimalFeas]⟩
  have hD : (DualFeas (0 : Matrix Unit Unit ℝ) (0 : Unit → ℝ)).Nonempty :=
    ⟨0, by simp [DualFeas]⟩
  have key := ((@h Unit Unit _ _ (0 : Matrix Unit Unit ℝ) 0 0).2.1 (Or.inl hP)).2.1 1
  have h1 := key.mpr ⟨hP, hD⟩
  have hS : {v : EReal | ∃ x ∈ PrimalFeas (0 : Matrix Unit Unit ℝ) (0 : Unit → ℝ),
      v = ((dotProduct (0 : Unit → ℝ) x : ℝ) : EReal)} = {0} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, zero_dotProduct, EReal.coe_zero]
    constructor
    · rintro ⟨x, -, rfl⟩; rfl
    · rintro rfl; exact ⟨0, by simp [PrimalFeas], rfl⟩
  rw [hS, sInf_singleton] at h1
  have : ((0 : ℝ) : EReal) = ((1 : ℝ) : EReal) := by simpa using h1
  have := EReal.coe_injective this
  norm_num at this

#print axioms solution
