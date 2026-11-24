-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpA.omS_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:40.419748+00:00
-- url     : https://prove2.me/submissions/d92b3feb-a4d1-4254-b1dc-0a52d09bf158

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
theorem _root_.solution (f : Sch l) : omS (eps : G l) f = -f := by
  show (((-1 : (Sch l →L[ℂ] Sch l)ˣ) : Sch l →L[ℂ] Sch l)) f = -f
  simp
end CompanionTheory.ThKR.Mp.MpA
