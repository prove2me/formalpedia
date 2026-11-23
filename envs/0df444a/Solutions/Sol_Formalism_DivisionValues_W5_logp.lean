-- Prove2me | solution 1 for Formalism.DivisionValues.W5.logp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:30.711235+00:00
-- url     : https://prove2.me/submissions/87c62458-8e7c-4501-a9be-b1a3112f7b8c

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Theorems.Thm_Formalism_DivisionValues_W5_log_le_near
import Theorems.Thm_Formalism_DivisionValues_W5_log_smooth

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
theorem _root_.solution (p : ℝ) (a b c d : ℕ) (e : ℝ) (hp : 0 < p)
    (he : (p - (2 : ℝ) ^ a * 3 ^ b * 5 ^ c * 7 ^ d) / ((2 : ℝ) ^ a * 3 ^ b * 5 ^ c * 7 ^ d) ≤ e) :
    Real.log p ≤ a * Real.log 2 + b * Real.log 3 + c * Real.log 5 + d * Real.log 7 + e := by
  have h := log_le_near p ((2 : ℝ) ^ a * 3 ^ b * 5 ^ c * 7 ^ d) hp (by positivity)
  rw [log_smooth] at h
  linarith
end Formalism.DivisionValues.W5
