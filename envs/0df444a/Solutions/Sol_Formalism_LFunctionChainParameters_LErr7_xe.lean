-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr7.xe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:39.137014+00:00
-- url     : https://prove2.me/submissions/b9d2f276-275b-4296-819e-9a17fe1e78ae

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsEventualPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ErrorExponentBelowOnesFalse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LErr7
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr
set_option linter.unusedVariables false
namespace Formalism.LFunctionChainParameters.LErr7
theorem _root_.solution : ((10 : ℝ) ^ 400) ^ ((1 : ℝ) / 100) = 10 ^ 4 := by
  rw [← Real.rpow_natCast (10 : ℝ) 400, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (10 : ℝ) 4]
  norm_num
end Formalism.LFunctionChainParameters.LErr7
