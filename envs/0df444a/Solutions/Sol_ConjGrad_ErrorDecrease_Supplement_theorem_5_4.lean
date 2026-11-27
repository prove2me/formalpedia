-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_5_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:31:26.787167+00:00
-- url     : https://prove2.me/submissions/742b6cea-db5a-4e21-953e-d9e63b56f29a

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 5:4 (Hestenes–Stiefel 1952, p. 415): the three-term recurrences (5:7a)–(5:8b) with
`bᵢ₋₁' = (aᵢ/aᵢ₋₁)bᵢ₋₁` (5:9). (5:7b) and (5:8b) are stated at the paper's index `i + 1 > 0`. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) :
    (cgIter A k x₀ 1).p = (1 + cgBeta A k x₀ 0) • (cgIter A k x₀ 0).p -
      cgAlpha A (cgIter A k x₀ 0) • (A *ᵥ (cgIter A k x₀ 0).p) ∧
    (∀ i : ℕ, (cgIter A k x₀ (i + 2)).p =
      (1 + cgBeta A k x₀ (i + 1)) • (cgIter A k x₀ (i + 1)).p -
        cgAlpha A (cgIter A k x₀ (i + 1)) • (A *ᵥ (cgIter A k x₀ (i + 1)).p) -
        cgBeta A k x₀ i • (cgIter A k x₀ i).p) ∧
    (cgIter A k x₀ 1).r = (cgIter A k x₀ 0).r -
      cgAlpha A (cgIter A k x₀ 0) • (A *ᵥ (cgIter A k x₀ 0).r) ∧
    (∀ i : ℕ, (cgIter A k x₀ (i + 2)).r =
      (1 + cgAlpha A (cgIter A k x₀ (i + 1)) / cgAlpha A (cgIter A k x₀ i) * cgBeta A k x₀ i) •
          (cgIter A k x₀ (i + 1)).r -
        cgAlpha A (cgIter A k x₀ (i + 1)) • (A *ᵥ (cgIter A k x₀ (i + 1)).r) -
        (cgAlpha A (cgIter A k x₀ (i + 1)) / cgAlpha A (cgIter A k x₀ i) * cgBeta A k x₀ i) •
          (cgIter A k x₀ i).r) := by
            have hr : ∀ i, (cgIter A k x₀ (i+1)).r = (cgIter A k x₀ i).r -
                cgAlpha A (cgIter A k x₀ i) • (A *ᵥ (cgIter A k x₀ i).p) := fun i => rfl
            have hp : ∀ i, (cgIter A k x₀ (i+1)).p = (cgIter A k x₀ (i+1)).r +
                cgBeta A k x₀ i • (cgIter A k x₀ i).p := fun i => rfl
            have h0 : (cgIter A k x₀ 0).p = (cgIter A k x₀ 0).r := rfl
            have key : ∀ i, (cgAlpha A (cgIter A k x₀ (i + 1)) / cgAlpha A (cgIter A k x₀ i) *
                cgBeta A k x₀ i) • (cgAlpha A (cgIter A k x₀ i) • (A *ᵥ (cgIter A k x₀ i).p)) =
                (cgAlpha A (cgIter A k x₀ (i + 1)) * cgBeta A k x₀ i) • (A *ᵥ (cgIter A k x₀ i).p) := by
              intro i
              rw [smul_smul]
              by_cases ha : cgAlpha A (cgIter A k x₀ i) = 0
              · have : cgBeta A k x₀ i = 0 ∨ A *ᵥ (cgIter A k x₀ i).p = 0 := by
                  unfold cgAlpha at ha
                  rcases div_eq_zero_iff.mp ha with h | h
                  · left; unfold cgBeta; rw [h, div_zero]
                  · right
                    have hp0 : (cgIter A k x₀ i).p = 0 := by
                      by_contra hne
                      have := hA.dotProduct_mulVec_pos hne
                      simp only [star_trivial] at this
                      linarith
                    rw [hp0, mulVec_zero]
                rcases this with h | h
                · rw [h]; simp
                · rw [h]; simp
              · congr 1
                field_simp
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [hp, hr, h0]; module
            · intro i
              rw [hp (i+1), hr (i+1), hp i, mulVec_add, mulVec_smul, hr i]
              module
            · rw [hr, h0]
            · intro i
              have k1 := key i
              have h1 := hr i
              rw [hr (i+1), hp i, mulVec_add, mulVec_smul]
              linear_combination (norm := module) k1 - (cgAlpha A (cgIter A k x₀ (i + 1)) /
                cgAlpha A (cgIter A k x₀ i) * cgBeta A k x₀ i) • h1
