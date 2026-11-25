-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model.hcomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:32:45.767441+00:00
-- url     : https://prove2.me/submissions/90e2f4ae-1a72-41cf-aefb-ab77255ecf09

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Theorems.Thm_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_Model_sum_abs_ge

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
theorem _root_.solution (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) : (D1 μ0 μ1 μ2 h).HComp C2 := by
  intro u0 u u'
  have h1 := sum_abs_ge h u
  have h2 := sum_abs_ge h u'
  have h3 : |h u - h u'| ≤ |h u| + |h u'| := abs_sub _ _
  have h5 := abs_nonneg EeV
  have h6 := abs_nonneg (muMV μ0)
  have h7 := abs_nonneg (μ1 - SgV)
  simp [D1, C2, Data.nT, LaV]
  linarith
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model
