-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.chain_sizes_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:17:51.976999+00:00
-- url     : https://prove2.me/submissions/34457ab0-9e4f-4dd5-a74d-f819e69f4f3b

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelText_family

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
theorem _root_.solution : ChainSizesTextEv := by
  intro ε h0 h1
  obtain ⟨x₀, hx₀⟩ := ModelText.family ε h0 h1
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨n, i, m, TT, T2, s1, s2, s3, s4, s5, s6, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hx₀ x hx
  have hc : (Fintype.card (ZMod n) : ℝ) = (n : ℝ) := by rw [ZMod.card]
  refine ⟨n, i, TT, inferInstance, m, Model.fM (ZMod n), ModelText.textData x ε m TT T2, ModelText.CF,
    XppTx x ε (Fintype.card (ZMod n)), Model.DA, fun _ => 0, ModelText.NF (ZMod n) x ε, TT, T2, fun _ => aTx x ε,
    ModelText.wF x ε m TT T2, Equiv.refl _, Model.ePM, ModelText.etaTx x ε, XpTx x ε, ModelText.thTx x ε,
    rfl, rfl, ⟨s1, s2, s3, s4, s5, s6⟩,
    ⟨rfl, rfl, rfl, rfl, ?_, rfl, (Real.log_exp _).symm, rfl, rfl, rfl, rfl⟩, ⟨?_, ?_⟩,
    ⟨le_refl _, le_refl _, le_refl _⟩, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
  · rw [hc]; rfl
  · rw [← hc]; rfl
  · rw [← hc]; rfl
end Formalism.LFunctionChainParameters.LChain
