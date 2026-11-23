-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.unipotent_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:27.583528+00:00
-- url     : https://prove2.me/submissions/50033fad-39c5-4794-bacc-b4a51ba658ed

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.EigenvalueLevelCeiling
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : UnipNum := by
  unfold UnipNum
  intro f r d dK δq hf hr hd hq
  have hr0 : 0 ≤ r - 1 := by linarith
  have hA : 0 ≤ f * r * (r - 1) / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hf (by linarith)) hr0) (by norm_num)
  have h1 : f * r * (r - 1) / 2 * (d + dK / δq) ≤ f * r * (r - 1) / 2 * (4 * d) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  have h2 : 0 ≤ f * r * d := mul_nonneg (mul_nonneg hf (by linarith)) hd
  have h3 : f * r * (r - 1) / 2 * (4 * d) = 2 * f * r ^ 2 * d - 2 * (f * r * d) := by ring
  linarith
end Formalism.EigenvalueLevelCeiling
