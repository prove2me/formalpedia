-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.share_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:51.588346+00:00
-- url     : https://prove2.me/submissions/fcc56290-dd42-4a59-922c-6854738fedd0

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
theorem _root_.solution : ShareNum := by
  unfold ShareNum
  intro dK d0 d U δq ep y del hU hδ hdK hd0 hep hey hy hdel hdel' h1 h2 h3
  rw [div_le_iff₀ hδ]
  have k1 : 7 / 8 * dK ≤ U * d0 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 8 - ep) hdK]
  have k2 : 7 / 8 * U ≤ δq := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 8 - y) hU.le]
  have k3 : 3 / 4 * d0 ≤ d := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 4 - del) hd0]
  have hd : 0 ≤ d := by linarith
  have k4 : d * (7 / 8 * U) ≤ d * δq := mul_le_mul_of_nonneg_left k2 hd
  have k5 : 3 / 4 * d0 * U ≤ d * U := mul_le_mul_of_nonneg_right k3 hU.le
  nlinarith
end Formalism.EigenvalueLevelCeiling
