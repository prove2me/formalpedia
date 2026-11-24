-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpA.dd_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:36.623013+00:00
-- url     : https://prove2.me/submissions/75afaede-6bf1-4fcb-a171-c8344579128a

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
theorem _root_.solution : dd (1 : Mat l) = 1 := by
  have h : upperParabolic (1 : Mat l) = 1 := by
    ext a b
    by_cases hab : a = b <;> simp [upperParabolic, Matrix.one_apply, hab]
  rw [dd, h, det_one]
end CompanionTheory.ThKR.Mp.MpA
