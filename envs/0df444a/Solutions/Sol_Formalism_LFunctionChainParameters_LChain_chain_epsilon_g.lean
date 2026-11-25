-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.chain_epsilon_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:43:07.060778+00:00
-- url     : https://prove2.me/submissions/35d483af-04f1-4d61-9c4b-6594fc87b560

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_chain_at_alt
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_x_large_eventually
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_core_exp_nonneg

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
theorem _root_.solution : ChainEpsG := by
  rintro eD eL ε ⟨K, cHH, eK, CL, x₀, h⟩
  obtain ⟨-, -, hε⟩ := core_exp_nonneg (h x₀ (le_refl _))
  obtain ⟨Cd, -, hAt⟩ := chain_at_alt
  obtain ⟨x₂, hx₂⟩ := x_large_eventually K cHH eK Cd CL ε hε
  exact ⟨max x₀ x₂, fun x hx => hAt eD eL ε x ⟨K, cHH, eK, CL, h x (le_trans (le_max_left _ _) hx),
    hx₂ x (le_trans (le_max_right _ _) hx)⟩⟩
end Formalism.LFunctionChainParameters.LChain
