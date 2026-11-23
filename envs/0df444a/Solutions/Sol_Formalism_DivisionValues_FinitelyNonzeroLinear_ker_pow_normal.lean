-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.ker_pow_normal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:12.243831+00:00
-- url     : https://prove2.me/submissions/90328a20-454b-488a-8a45-051bb2d5e5f6

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_Fnl_zero
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_vec_zero_of_form
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_adj_symm
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_ker_of_adj_mul
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ}
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution (hH : Hc.PosDef) {N N' : Matrix (Fin n) (Fin n) ℂ}
    (hadj : Nᴴ * Hc = Hc * N') (hc : N * N' = N' * N) (k : ℕ) (x : Fin n → ℂ)
    (h : (N ^ k) *ᵥ x = 0) : N *ᵥ x = 0 := by
  have hadj' := adj_symm hH hadj
  have key : ∀ y, N *ᵥ (N *ᵥ y) = 0 → N *ᵥ y = 0 := by
    intro y hy
    have h1 : N' *ᵥ (N *ᵥ y) = 0 := ker_of_adj_mul hH hadj' _ (by
      rw [hc, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero])
    apply vec_zero_of_form hH
    have e : star (N *ᵥ y) ⬝ᵥ Hc *ᵥ (N *ᵥ y) = star y ⬝ᵥ (Nᴴ * Hc * N) *ᵥ y := by
      simp only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]
    rw [e, hadj, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1]
    simp
  induction k with
  | zero =>
    simp at h
    simp [h]
  | succ k ih =>
    rcases k with _ | m
    · simpa using h
    · apply ih
      have h3 : N *ᵥ (N *ᵥ ((N ^ m) *ᵥ x)) = 0 := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← pow_succ', ← pow_succ']
        exact h
      have h4 := key _ h3
      rwa [Matrix.mulVec_mulVec, ← pow_succ'] at h4
end Formalism.DivisionValues.FinitelyNonzeroLinear
