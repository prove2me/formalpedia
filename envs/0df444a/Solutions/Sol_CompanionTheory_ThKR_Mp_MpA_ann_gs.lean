-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpA.ann_gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:40.387144+00:00
-- url     : https://prove2.me/submissions/4e8ef66a-ae4d-4b63-b962-2515254eef5f

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousTo
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_fderiv_gs
import Theorems.Thm_GlobalTheory_RealWeil_dRho_single_inl
import Theorems.Thm_GlobalTheory_RealWeil_dRho_single_inr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open CompanionTheory.ThKR.Mp.MpA
namespace CompanionTheory.ThKR.Mp.MpA
theorem _root_.solution : Ann (1 : Sp l).1 (gs l) := fun j => by
  have e1 : ((1 : Sp l) : Mat l) = 1 := rfl
  rw [e1, one_mulVec, one_mulVec]
  ext x
  rw [SchwartzMap.smul_apply, dRho_single_inr, dRho_single_inl, lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  linear_combination fderiv_gs j x - (2 * π * (x j : ℂ) * gs l x) * I_sq
end CompanionTheory.ThKR.Mp.MpA
