-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.chain_weighted_mean_to_unit_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:52:51.756946+00:00
-- url     : https://prove2.me/submissions/a79f288e-34fa-4490-aac6-4e68d7dfa536

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_chain_top_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_proposition_final_minimum


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
theorem _root_.solution : ChainGivesRiemannHypothesis := by
  obtain ⟨Cd, hCd, hFin⟩ := proposition_final_minimum
  refine ⟨Cd, hCd, fun eD eL ε₁ hε₁ h => hFin (eD + eL + 3) ε₁ hε₁ ?_⟩
  intro ε h0 h1
  obtain ⟨x₀, hx₀⟩ := h ε h0 h1
  exact ⟨x₀, fun x hx => chain_top_bound Cd eD eL ε x (hx₀ x hx)⟩
end Formalism.LFunctionChainParameters.LChain
