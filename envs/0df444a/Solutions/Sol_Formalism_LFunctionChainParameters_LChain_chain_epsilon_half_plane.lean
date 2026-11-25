-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.chain_epsilon_half_plane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:14:02.156496+00:00
-- url     : https://prove2.me/submissions/ad3a21b8-de23-4779-87a9-01105f6a94ef

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_core_exp_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_chain_epsilon_g
import Theorems.Thm_Formalism_LFunctionChainParameters_ConditionalMainTheorem_landau_zero_free_half_plane


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
theorem _root_.solution : ChainEpsHalfPlane := by
  intro eD eL ε h s hs
  obtain ⟨x₁, hx₁⟩ := chain_epsilon_g eD eL ε h
  obtain ⟨K, cHH, eK, CL, x₀, h⟩ := h
  obtain ⟨h1, h2, hε⟩ := core_exp_nonneg (h x₀ (le_refl _))
  have hpos : 0 ≤ (eD + eL + 6) * ε := by positivity
  by_cases hsmall : (eD + eL + 6) * ε < 1 / 2
  · exact landau_zero_free_half_plane _ (by linarith) (by linarith) x₁ hx₁ s hs
  · exact riemannZeta_ne_zero_of_one_le_re (by linarith)
end Formalism.LFunctionChainParameters.LChain
