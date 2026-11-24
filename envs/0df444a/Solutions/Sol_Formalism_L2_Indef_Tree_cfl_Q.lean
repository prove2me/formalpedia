-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.cfl_Q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:38.497497+00:00
-- url     : https://prove2.me/submissions/e06cb445-bbe5-4b71-aae3-b3def25c2b60

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
theorem _root_.solution (E CfL PPp kap lrdk : ℝ) (hE : |E| ≤ PPp * kap) (h0 : 0 ≤ CfL) (h1 : CfL ≤ kap) (hl : 0 ≤ lrdk) :
    |2 * (E - CfL)| ≤ 2 * (PPp * kap) + 2 * kap + 2 * lrdk := by
  rw [abs_le] at hE ⊢; constructor <;> linarith
end Formalism.L2.Indef.Tree
