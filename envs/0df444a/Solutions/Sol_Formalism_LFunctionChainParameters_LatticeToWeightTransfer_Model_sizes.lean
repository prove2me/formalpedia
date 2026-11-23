-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model.sizes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:24.889014+00:00
-- url     : https://prove2.me/submissions/a081ae61-3860-4434-8ebc-76a50f05e842

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices

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
theorem _root_.solution (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) :
    SizesPrim (D1 μ0 μ1 μ2 h) C2 |RdV| 1 (fun _ _ => Q0 μ0 μ1) := by
  refine ⟨le_refl _, by norm_num [C2], by simp [D1], by simp [D1], fun u0 u => ⟨le_refl _, ?_, ?_⟩⟩
  · simp [D1, Q0, Data.nT]; norm_num
  · have h1 := le_abs_self RdV
    have h2 := abs_nonneg RdV
    show RdV ≤ 4 * |RdV|
    linarith
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model
