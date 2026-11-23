-- Prove2me | solution 1 for Formalism.DivisionValues.W5.log_three_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:41.131514+00:00
-- url     : https://prove2.me/submissions/ed18bd93-a48f-4b86-a28e-92bcb35ba138

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Theorems.Thm_Formalism_DivisionValues_W5_logp

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
theorem _root_.solution : Real.log 3 ≤ (19 * Real.log 2 + 7153 / 524288) / 12 := by
  have h := logp ((3 : ℝ) ^ 12) 19 0 0 0 (7153 / 524288) (by positivity) (by norm_num)
  rw [Real.log_pow] at h
  push_cast at h
  linarith
end Formalism.DivisionValues.W5
