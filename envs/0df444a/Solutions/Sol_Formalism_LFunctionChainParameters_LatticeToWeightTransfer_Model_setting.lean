-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model.setting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:31.18605+00:00
-- url     : https://prove2.me/submissions/0338a7e6-982c-4db7-b0fa-b471b2473433

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Theorems.Thm_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_Model_HHV_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LatticeToWeightTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model
namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model
theorem _root_.solution (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) (hμ : μ0 ≤ μ1) : (D1 μ0 μ1 μ2 h).HidaSetting C2 := by
  refine ⟨HHV_pos μ0 μ2 h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => hμ, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [D1, C2, Real.pi_pos]
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model
