-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PhiMonotonicityLemmas.corollary_final_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:20:11.585317+00:00
-- url     : https://prove2.me/submissions/bd96e2fe-0cae-481e-bf26-f22009f00df0

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeExcessBoundExponentZero
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Theorems.Thm_Formalism_LFunctionChainParameters_PhiMonotonicityLemmas_corollary_model_side_condition

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
theorem _root_.solution : CorFinalModel := by
  have hp : (2 : ℝ) ^ (5 : ℝ) = 32 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hn : (2 : ℝ) ^ (-(5 : ℝ)) = 1 / 32 := by
    rw [Real.rpow_neg (by norm_num), hp]; norm_num
  have hs1 : Real.sqrt (1 / 36864) = 1 / 192 := by
    rw [show (1 / 36864 : ℝ) = (1 / 192) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hs2 : Real.sqrt (2 * (1 / 131072)) = 1 / 256 := by
    rw [show (2 * (1 / 131072) : ℝ) = (1 / 256) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨0 + 1 + ErrF (1 / 8) 1 32 (5 * (1 / 32) + 3 * (1 / 192)) (2 * (1 / 131072)), 0, 1, 1 / 8,
    1, 1, 32, 5 * (1 / 32) + 3 * (1 / 192), 2 * (1 / 131072), 1 / 131072, 1 / 36864, 3, 1, 2, 5,
    le_refl _, by norm_num, by norm_num, by norm_num, ?_, by norm_num, le_refl _, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, rfl, by norm_num, ?_, by norm_num,
    corollary_model_side_condition, by ring⟩
  · rw [hp]; norm_num
  · rw [hn]; norm_num
  · rw [hn, hs1]
  · rw [hn, hs1, hs2]; norm_num
end Formalism.LFunctionChainParameters.PhiMonotonicityLemmas
