-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.exists_data_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:22.114702+00:00
-- url     : https://prove2.me/submissions/d2e5f98b-5144-47db-8a3d-a6f0684a745b

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_data_completion_bounds

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
variable {U0 : Type} [Fintype U0] {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
namespace Formalism.LFunctionChainParameters.LChain
theorem _root_.solution : DataCompletion := by
  intro U0 _ W Top _ m f D0 C Xpp hx hb ha hb' hk hLa hB0 hXpp hf haT hw hC hS0 hS1 hTop
  exact ⟨compl D0 C, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl,
    data_completion_bounds D0 C Xpp hx hb ha hb' hk hLa hB0 hXpp hf haT hw hC hS0 hS1 hTop⟩
end Formalism.LFunctionChainParameters.LChain
