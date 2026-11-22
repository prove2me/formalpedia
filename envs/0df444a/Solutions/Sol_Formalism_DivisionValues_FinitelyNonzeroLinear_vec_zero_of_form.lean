-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.vec_zero_of_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:50:51.801834+00:00
-- url     : https://prove2.me/submissions/b53e8252-27fd-43b7-b5ea-406402628f6d

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist

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
theorem _root_.solution (hH : Hc.PosDef) (x : Fin n → ℂ) (h : star x ⬝ᵥ Hc *ᵥ x = 0) : x = 0 := by
  by_contra hx
  have hp := hH.dotProduct_mulVec_pos hx
  rw [h] at hp
  exact lt_irrefl _ hp
end Formalism.DivisionValues.FinitelyNonzeroLinear
