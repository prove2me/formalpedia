-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.top_each_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:21:12.542946+00:00
-- url     : https://prove2.me/submissions/1a19fe90-60ba-4f02-b0a7-ddd730040651

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_each_unit_bound_statement


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
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.ConditionalMainTheorem Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.LChain
theorem _root_.solution : CoreTopEach := by
  intro H _ _ _ W _ _ Top _ m f Dd C Xpp D ell N TT a w eT eP hId hLed u0
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hLed
  rw [← hId.2.2.2.2 u0]
  exact each_unit_bound_statement Dd C Xpp l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 u0
end Formalism.LFunctionChainParameters.LChain
