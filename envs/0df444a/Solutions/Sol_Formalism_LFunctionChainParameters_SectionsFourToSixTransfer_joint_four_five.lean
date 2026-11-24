-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.joint_four_five
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:00:13.889286+00:00
-- url     : https://prove2.me/submissions/99d618f2-4f25-49d8-bc56-505b0dfb6ef1

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_z_to_slopes
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_proposition_to_log_t_upper
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_proposition_to_count

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
namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
theorem _root_.solution : SlopeCountJoint := by
  intro U0 W Top _ m f D C cZ cL Sc LZ c5 Gam X hZW hZ hCW h5 hV hLW hC1 hC2
  exact ⟨z_to_slopes D C cZ cL (c5 + 1) Sc LZ hZW (proposition_to_log_t_upper D c5 Gam X hCW h5 hLW) hZ hC1,
    proposition_to_count D C c5 Gam X hCW h5 hV hLW hC2⟩
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
