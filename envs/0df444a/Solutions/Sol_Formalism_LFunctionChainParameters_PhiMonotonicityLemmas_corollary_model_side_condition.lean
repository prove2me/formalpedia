-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PhiMonotonicityLemmas.corollary_model_side_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:29:29.209195+00:00
-- url     : https://prove2.me/submissions/e432fa90-24de-4647-b9a9-b7b9d64c6d34

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeExcessBoundExponentZero
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real Filter
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PhiMonotonicityLemmas
namespace Formalism.LFunctionChainParameters.PhiMonotonicityLemmas
theorem _root_.solution :
    (0 + 1 + ErrF (1 / 8) 1 32 (5 * (1 / 32) + 3 * (1 / 192)) (2 * (1 / 131072))) - 0 ≤ (32 : ℝ) := by
  have hs2 : Real.sqrt (2 * (1 / 131072)) = 1 / 256 := by
    rw [show (2 * (1 / 131072) : ℝ) = (1 / 256) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hl : Real.log (1 + 32 / 1) ≤ 6 * Real.log 2 := by
    rw [show (6 : ℝ) * Real.log 2 = Real.log (2 ^ 6) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h2 := Real.log_two_lt_d9
  unfold ErrF phi
  rw [hs2]
  norm_num at hl ⊢
  linarith
end Formalism.LFunctionChainParameters.PhiMonotonicityLemmas
