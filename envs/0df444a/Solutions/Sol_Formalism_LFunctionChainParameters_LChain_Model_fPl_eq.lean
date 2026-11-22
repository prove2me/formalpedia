-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.Model.fPl_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:13:08.41086+00:00
-- url     : https://prove2.me/submissions/f91952df-f5fc-4671-930d-6be428be5f9d

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain

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
open Formalism.LFunctionChainParameters.LChain.Model
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.LChain.Model
theorem _root_.solution : fPl H = 2 * (Fintype.card H : ℝ) := by
  unfold fPl PhiSet
  have : (univ.filter (InPhi (H := H))) = (({((0:ZMod 2),(0:ZMod 2)), (0,1)} : Finset E0) ×ˢ (univ : Finset H)) := by
    ext ⟨⟨a, b⟩, h⟩
    simp only [mem_filter, mem_univ, true_and, InPhi, mem_product, mem_insert, mem_singleton, Prod.mk.injEq, and_true]
    revert a b; decide
  rw [this, card_product]
  simp [Finset.card_univ]
end Formalism.LFunctionChainParameters.LChain.Model
