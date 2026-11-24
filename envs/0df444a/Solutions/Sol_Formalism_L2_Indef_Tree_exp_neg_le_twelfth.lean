-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.exp_neg_le_twelfth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:50:08.635075+00:00
-- url     : https://prove2.me/submissions/ae2217ec-c94d-4dbc-85ba-3005f9c4aca7

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
theorem _root_.solution (t : ℝ) (ht : 3 ≤ t) : Real.exp (-t) ≤ 1 / 12 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h27 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h1.le 3
  have h12 : 12 ≤ Real.exp 3 := by rw [h3]; linarith [show (12 : ℝ) ≤ 2.7 ^ 3 by norm_num]
  have hm : Real.exp (-t) ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by linarith)
  have e3 : Real.exp (-3) * Real.exp 3 = 1 := by rw [← Real.exp_add]; norm_num
  have hp : 0 < Real.exp (-3) := Real.exp_pos _
  nlinarith
end Formalism.L2.Indef.Tree
