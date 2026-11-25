-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model.count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:16:51.680749+00:00
-- url     : https://prove2.me/submissions/04e56e02-9ca6-460b-9d31-4a1325378a05

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Theorems.Thm_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_Model_LaV_nonneg

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
theorem _root_.solution (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) : Count5 (D1 μ0 μ1 μ2 h) C2 := by
  intro u0 u
  have h4 := LaV_nonneg μ0 μ1 h
  have h5 : 0 ≤ Real.log 211 := Real.log_nonneg (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simp [D1, C2, Real.pi_ne_zero]
    linarith
  · simp [D1, C2]
  · intro u'
    simp [D1, C2]
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model
