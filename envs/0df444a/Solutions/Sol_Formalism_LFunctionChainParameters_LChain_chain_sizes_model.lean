-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.chain_sizes_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:17:56.728308+00:00
-- url     : https://prove2.me/submissions/66bd30f2-adae-4187-aaf2-2ea5bbe04a1a

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_Model_sizesModelAt

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
theorem _root_.solution : ChainSizesModel :=
  ⟨ZMod 65536, inferInstance, inferInstance, inferInstance, Model.sizesModelAt (ZMod.card 65536)⟩
end Formalism.LFunctionChainParameters.LChain
