-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.example_slope_bound_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:13:09.346284+00:00
-- url     : https://prove2.me/submissions/312238b1-80ed-464b-9d38-a166a55293bc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundSingleLiftOfDefinitions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField Formalism.HN
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
attribute [instance] SlopeBoundParameters.fPl SlopeBoundParameters.dimNeZero
attribute [instance] SlopeBoundLiftData.fι SlopeBoundLiftData.nι
namespace Formalism.L2.Indef.Tree
theorem _root_.solution (v0 : InfinitePlace Examples₂.K3) :
    ∃ N : IndefNum (Examples₂.one.base Examples₂.K3 v0), ¬ (Examples₂.one.dat Examples₂.K3 v0).L3 N := by
  refine ⟨{ Examples₂.one.num Examples₂.K3 v0 with
    l3 := fun _ => Formalism.DivisionValues.lcv (Examples₂.fr Examples₂.K3 1) (Examples₂.sl Examples₂.K3 1) / ((1 : ℕ) : ℝ) - 1 }, fun h => ?_⟩
  have := h ()
  change Formalism.DivisionValues.lcv (Examples₂.fr Examples₂.K3 1) (Examples₂.sl Examples₂.K3 1) / ((1 : ℕ) : ℝ) ≤
    Formalism.DivisionValues.lcv (Examples₂.fr Examples₂.K3 1) (Examples₂.sl Examples₂.K3 1) / ((1 : ℕ) : ℝ) - 1 at this
  linarith
end Formalism.L2.Indef.Tree
