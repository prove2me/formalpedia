-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.Model.hak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:39:59.958802+00:00
-- url     : https://prove2.me/submissions/a1460d7e-e745-4b02-b37b-d5e00cfe45bc

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_Model_exp_forty_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer
open Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.Model
namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.Model
theorem _root_.solution : Real.exp 40 / Real.exp 2 = Real.exp 2 * Real.exp 36 := by
  rw [exp_forty_eq]; field_simp
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.Model
