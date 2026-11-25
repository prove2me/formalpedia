-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:37.364805+00:00
-- url     : https://prove2.me/submissions/82a922ed-bfee-4bdd-b767-600d3107d38b

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousTo
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_G_ext
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_ann_gs
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_gs_zero
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_dd_one
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_om_eps
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_omS_eps
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_pr_eps
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_eps_ne
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_om_of_omS
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_scalar
import Theorems.Thm_CompanionTheory_ThKF_E_exists_rho
import Theorems.Thm_CompanionTheory_ThKF_E_toLp_rho
import Theorems.Thm_CompanionTheory_ThKR_Mp_omS_nrm
import Theorems.Thm_CompanionTheory_ThKR_Mp_om_rho
import Theorems.Thm_CompanionTheory_ThKR_Mp_om_sch
import Theorems.Thm_GlobalTheory_RealWeil_schwartzToL2_apply


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
open MpA
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution : Ker l := by
  refine ⟨eps, eps_ne, fun g => ⟨fun hg => ?_, ?_⟩, om_eps⟩
  · have hsurj : Function.Surjective (omS g) := fun f => ⟨omS g⁻¹ f, by
      show (omS g * omS g⁻¹) f = f
      rw [← map_mul, mul_inv_cancel, map_one]; rfl⟩
    have hpg : ((pr g : Sp l) : Mat l) = 1 := by rw [hg]; rfl
    have hI : Impl id (omS g).toLinearMap := by
      refine ⟨fun f => ?_, fun w f k hk => ?_⟩
      · show ‖schwartzToL2 l (omS g f)‖ = ‖schwartzToL2 l f‖
        rw [← om_sch, LinearIsometryEquiv.norm_map]
      · obtain ⟨k', hk'⟩ := exists_rho w (omS g f)
        have e : omS g k = k' := by
          apply injective_toLp 2 volume
          calc (omS g k).toLp 2 volume = om g (k.toLp 2 volume) := (om_sch g k).symm
            _ = om g (rho w (f.toLp 2 volume)) := by rw [toLp_rho hk]
            _ = rho w (om g (f.toLp 2 volume)) := by rw [om_rho, hpg, one_mulVec]
            _ = rho w ((omS g f).toLp 2 volume) := by rw [← schwartzToL2_apply, om_sch]; rfl
            _ = k'.toLp 2 volume := (toLp_rho hk').symm
        show ⇑(omS g k) = rhoFun w (omS g f)
        rw [e, hk']
    obtain ⟨c, hc⟩ := hI.scalar hsurj
    have hc' : ∀ f, omS g f = c • f := hc
    have hn := omS_nrm g 1 (gs l) ann_gs
    have e1 : ((1 : Sp l) : Mat l) = 1 := rfl
    rw [hpg, e1, Matrix.one_mul, dd_one, hc', SchwartzMap.smul_apply, gs_zero] at hn
    have hc2 : (c - 1) * (c + 1) = 0 := by linear_combination hn
    rcases mul_eq_zero.1 hc2 with h | h
    · left
      have hc1 : c = 1 := sub_eq_zero.1 h
      refine G_ext (by rw [hg, map_one]) (LinearIsometryEquiv.ext fun F => ?_) (ContinuousLinearMap.ext fun f => ?_)
      · rw [om_of_omS hc', hc1, one_smul, map_one]; rfl
      · rw [hc', hc1, one_smul, map_one]; rfl
    · right
      have hc1 : c = -1 := eq_neg_of_add_eq_zero_left h
      refine G_ext (by rw [hg, pr_eps]) (LinearIsometryEquiv.ext fun F => ?_) (ContinuousLinearMap.ext fun f => ?_)
      · rw [om_of_omS hc', hc1, om_eps, neg_one_smul]
      · rw [hc', hc1, omS_eps, neg_one_smul]
  · rintro (rfl | rfl)
    · exact map_one _
    · exact pr_eps
end CompanionTheory.ThKR.Mp
