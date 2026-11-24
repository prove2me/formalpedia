-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpA.eps_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:29.094214+00:00
-- url     : https://prove2.me/submissions/6b105069-0224-447d-9281-4d8d96a5bb03

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousTo
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_omS_eps
import Theorems.Thm_CompanionTheory_ThKF_E_exists_ne_zero
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
theorem _root_.solution : (eps : G l) ≠ 1 := by
  intro h
  obtain ⟨φ, hφ⟩ := exists_ne_zero (0 : EuclideanSpace ℝ l)
  have h1 : omS (eps : G l) φ = omS (1 : G l) φ := by rw [h]
  rw [omS_eps, map_one, ContinuousLinearMap.one_apply] at h1
  have h2 : -φ 0 = φ 0 := by
    have := congrArg (fun u : Sch l => u 0) h1
    simpa using this
  exact hφ (by linear_combination (-1 / 2 : ℂ) * h2)
end CompanionTheory.ThKR.Mp.MpA
