-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.exampleSingleLift_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:42:08.720113+00:00
-- url     : https://prove2.me/submissions/0ef79c65-9844-4554-b417-3302361dace3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundSingleLiftOfDefinitions
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Finset Module NumberField Formalism.HN
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
attribute [instance] SlopeBoundParameters.fPl SlopeBoundParameters.dimNeZero
attribute [instance] SlopeBoundLiftData.fι SlopeBoundLiftData.nι
namespace Formalism.L2.Indef.Tree
theorem _root_.solution : Examples₂.sl Examples₂.K3 1 ≠ ⊥ := by
  intro h
  have hm : Examples₂.sb Examples₂.K3 1 0 ∈ Examples₂.sl Examples₂.K3 1 := Submodule.subset_span ⟨0, rfl⟩
  rw [h, Submodule.mem_bot] at hm
  have := congrFun hm 0
  simp [Examples₂.sb] at this
end Formalism.L2.Indef.Tree
