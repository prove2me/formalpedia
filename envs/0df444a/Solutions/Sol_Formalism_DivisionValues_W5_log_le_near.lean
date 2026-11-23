-- Prove2me | solution 1 for Formalism.DivisionValues.W5.log_le_near
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:58.855864+00:00
-- url     : https://prove2.me/submissions/0e980100-894f-4fa0-8e6e-1d7979d47bc9

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares

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
open Formalism.DivisionValues.W5
namespace Formalism.DivisionValues.W5
theorem _root_.solution (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    Real.log p ≤ Real.log q + (p - q) / q := by
  have h := Real.log_le_sub_one_of_pos (div_pos hp hq)
  rw [Real.log_div hp.ne' hq.ne'] at h
  have : (p - q) / q = p / q - 1 := by field_simp
  linarith
end Formalism.DivisionValues.W5
