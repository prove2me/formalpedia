-- Prove2me | solution 1 for Formalism.DivisionValues.W5.place_sum_over_primes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:41.747437+00:00
-- url     : https://prove2.me/submissions/41771f7a-f677-4da2-b1d8-d33e9a8fbbdd

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
theorem _root_.solution : Real.log 7 ≤ (4 * Real.log 2 + Real.log 3 + 1 / 48) / 2 := by
  have h := logp ((7 : ℝ) ^ 2) 4 1 0 0 (1 / 48) (by positivity) (by norm_num)
  rw [Real.log_pow] at h
  push_cast at h
  linarith
end Formalism.DivisionValues.W5
