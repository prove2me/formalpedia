-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.x_large_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:26.225739+00:00
-- url     : https://prove2.me/submissions/168609c4-e28a-4cd1-9ec0-40bba41a5a16

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_moveCostEv
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_le_rpow_26
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_large_x_eventually


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
theorem _root_.solution : XLargeEv := by
  intro K cHH eK Cd CL ε hε
  obtain ⟨x₁, hx₁⟩ := large_x_eventually ε K cHH eK hε
  obtain ⟨x₂, hx₂⟩ := moveCostEv Cd CL ε hε
  refine ⟨max (max x₁ x₂) (max 3 ((26 : ℝ) ^ (8 / (3 * ε)))), fun x hx => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  · exact le_rpow_26 ε x hε (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx)
  · exact hx₁ x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)
  · exact hx₂ x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)
end Formalism.LFunctionChainParameters.LChain
