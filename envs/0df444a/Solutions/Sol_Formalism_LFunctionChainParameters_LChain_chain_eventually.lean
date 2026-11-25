-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.chain_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:14:07.583924+00:00
-- url     : https://prove2.me/submissions/645abad0-967d-43c6-873a-827a8381f84a

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_chain_weighted_mean_to_unit_weight
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_x_large_eventually

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
theorem _root_.solution : ChainEventualGivesRiemannHypothesis := by
  obtain ⟨Cd, -, hChain⟩ := chain_weighted_mean_to_unit_weight
  intro eD eL ε₁ hε₁ h
  refine hChain eD eL ε₁ hε₁ ?_
  intro ε h0 h1
  obtain ⟨K, cHH, eK, CL, x₀, hx₀⟩ := h ε h0 h1
  obtain ⟨x₁, hx₁⟩ := x_large_eventually K cHH eK Cd CL ε h0
  exact ⟨max x₀ x₁, fun x hx => ⟨K, cHH, eK, CL, hx₀ x (le_trans (le_max_left _ _) hx),
    hx₁ x (le_trans (le_max_right _ _) hx)⟩⟩
end Formalism.LFunctionChainParameters.LChain
