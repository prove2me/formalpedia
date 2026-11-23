-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.eq_zero_of_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:11.740772+00:00
-- url     : https://prove2.me/submissions/395b7955-2ec6-4531-8671-7909168b38b0

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
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
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {n m : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ} (hH : Hc.PosDef)
    (F : Matrix (Fin n) (Fin m) ℂ) (h : Fᴴ * Hc * F = 0) : F = 0 := by
  have key : ∀ w, star (F *ᵥ w) ⬝ᵥ Hc *ᵥ (F *ᵥ w) = star w ⬝ᵥ (Fᴴ * Hc * F) *ᵥ w := by
    intro w
    simp only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h0 : ∀ w, F *ᵥ w = 0 := by
    intro w
    by_contra hw
    have hpos := hH.dotProduct_mulVec_pos hw
    rw [key, h] at hpos
    simp at hpos
  ext i k
  have := congrFun (h0 (Pi.single k 1)) i
  simpa [Matrix.mulVec_single_one] using this
end Formalism.DivisionValues.FinitelyNonzeroLinear
