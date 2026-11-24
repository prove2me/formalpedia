-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpA.gs_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:38.636886+00:00
-- url     : https://prove2.me/submissions/ae953a48-3304-4903-8dc7-636d19a6b70b

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousTo
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open CompanionTheory.ThKR.Mp.MpA
namespace CompanionTheory.ThKR.Mp.MpA
theorem _root_.solution : gs l 0 = 1 := by simp
end CompanionTheory.ThKR.Mp.MpA
