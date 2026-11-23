-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.form_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:59.719492+00:00
-- url     : https://prove2.me/submissions/437ac37f-ae0f-459a-b2f5-50a6ca9cf243

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
theorem _root_.solution (c : ℂ) (u v : Fin n → ℂ) :
    star u ⬝ᵥ Hc *ᵥ (c • v) = c * (star u ⬝ᵥ Hc *ᵥ v) := by
  simp [Matrix.mulVec_smul]
end Formalism.DivisionValues.FinitelyNonzeroLinear
