-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.ker_of_adj_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:40.604798+00:00
-- url     : https://prove2.me/submissions/1dfba043-fc13-443c-8290-3a81a680872a

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_vec_zero_of_form

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
    (hadj : Nᴴ * Hc = Hc * N') (y : Fin n → ℂ) (h : (N' * N) *ᵥ y = 0) : N *ᵥ y = 0 := by
  apply vec_zero_of_form hH
  have e : star (N *ᵥ y) ⬝ᵥ Hc *ᵥ (N *ᵥ y) = star y ⬝ᵥ (Nᴴ * Hc * N) *ᵥ y := by
    simp only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  rw [e, hadj, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, h]
  simp
end Formalism.DivisionValues.FinitelyNonzeroLinear
