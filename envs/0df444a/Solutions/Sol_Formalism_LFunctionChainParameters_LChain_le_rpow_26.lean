-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.le_rpow_26
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:06.878813+00:00
-- url     : https://prove2.me/submissions/26f903c3-2d58-42fd-ac07-38449718b57b

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.LChain
theorem _root_.solution (ε x : ℝ) (hε : 0 < ε) (h1 : (26 : ℝ) ^ (8 / (3 * ε)) ≤ x) : 26 ≤ x ^ (3 * ε / 8) := by
  have h2 : 0 ≤ 3 * ε / 8 := by positivity
  have h3 := Real.rpow_le_rpow (by positivity) h1 h2
  rw [← Real.rpow_mul (by norm_num)] at h3
  have h4 : 8 / (3 * ε) * (3 * ε / 8) = 1 := by field_simp
  rwa [h4, Real.rpow_one] at h3
end Formalism.LFunctionChainParameters.LChain
