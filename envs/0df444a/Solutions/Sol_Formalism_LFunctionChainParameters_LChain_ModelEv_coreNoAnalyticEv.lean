-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.ModelEv.coreNoAnalyticEv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:53:00.296328+00:00
-- url     : https://prove2.me/submissions/1e9faea4-3575-4815-8ba7-e9b17f8f2940

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelEv_coreOfSizes
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelEv_sizesEv

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
open Formalism.LFunctionChainParameters.LChain.ModelEv
open Model
namespace Formalism.LFunctionChainParameters.LChain.ModelEv
theorem _root_.solution : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ChainCoreNoAnalytic 1 1 1 1 2 ε x ∧ XLarge 1 1 2 0 0 ε x := by
  intro ε h0 h1
  obtain ⟨x₀, hx₀⟩ := sizesEv ε h0 h1
  exact ⟨x₀, fun x hx => ⟨coreOfSizes (hx₀ x hx).1, (hx₀ x hx).2⟩⟩
end Formalism.LFunctionChainParameters.LChain.ModelEv
