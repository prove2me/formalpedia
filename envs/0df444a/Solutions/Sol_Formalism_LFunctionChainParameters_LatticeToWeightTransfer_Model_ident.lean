-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model.ident
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:29:29.580102+00:00
-- url     : https://prove2.me/submissions/151bd45f-62f9-456d-b641-33f877bce509

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
    PlaceSumIdentities (D1 μ0 μ1 μ2 h) (toP (D1 μ0 μ1 μ2 h) (fun _ _ => Q0 μ0 μ1)) := by
  intro u0 u
  refine ⟨rfl, rfl, fun j => ?_⟩
  have : j = 0 := Subsingleton.elim _ _
  subst this
  rfl
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model
