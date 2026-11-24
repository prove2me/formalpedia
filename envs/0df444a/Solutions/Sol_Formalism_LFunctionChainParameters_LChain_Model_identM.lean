-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.Model.identM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:29:28.764897+00:00
-- url     : https://prove2.me/submissions/350c70ff-bca1-446a-b6f4-523f59e399a3

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
theorem _root_.solution : Ident (modelData (H := H)) DA 1048576 (fun _ => 0) univ aM wM (Equiv.refl _) ePM := by
  refine ⟨fun τ => ?_, fun u0 j ρ => ?_, ?_, ?_, fun u0 => ?_⟩
  · simp only [modelData, aM]
  · simp only [modelData]
  · simp only [modelData]
  · simp only [modelData, Complex.zero_re]
  · simp only [modelData]
end Formalism.LFunctionChainParameters.LChain.Model
