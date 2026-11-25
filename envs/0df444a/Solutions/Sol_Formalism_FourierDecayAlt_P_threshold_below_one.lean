-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.threshold_below_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:51:34.128156+00:00
-- url     : https://prove2.me/submissions/1fbedee1-9ee3-4875-90d8-cfebffcd8a6b

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdBelowOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx11
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : ThresholdBelowOne := by
  intro m C c₂ κ N I A hκ hA hc
  unfold Sz.lamThreshold
  have e : 2 * (1 - 1) + 1 - 1 = 0 := by norm_num
  rw [e, pow_zero, mul_one]
  exact mul_le_mul_of_nonneg_right hc (by positivity)
end Formalism.FourierDecayAlt.P
