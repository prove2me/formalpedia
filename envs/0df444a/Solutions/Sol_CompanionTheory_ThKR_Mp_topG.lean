-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.topG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:37:51.142107+00:00
-- url     : https://prove2.me/submissions/f3833714-68a6-45ea-be22-8ae984711dcd

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousTo
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_continuous_to
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_sp_mul
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_sp_inv
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_om_cont2
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_om_mul
import Theorems.Thm_CompanionTheory_ThKR_Mp_continuous_om
import Theorems.Thm_CompanionTheory_ThKR_Mp_continuous_pr
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
open MpA
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution : TopG l := by
  have hm : ContinuousMul (G l) := ⟨continuous_to (by
      simp only [map_mul]
      exact sp_mul (continuous_pr.comp continuous_fst) (continuous_pr.comp continuous_snd)) fun f => by
      simp only [om_mul]
      exact om_cont2.comp (continuous_fst.prodMk ((continuous_om f).comp continuous_snd))⟩
  have hi : ContinuousInv (G l) := ⟨continuous_to (by
      simp only [map_inv]
      exact sp_inv continuous_pr) fun f => by
      refine continuous_iff_continuousAt.2 fun g0 => ?_
      rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
      obtain ⟨v, hv⟩ : ∃ v, om g0⁻¹ f = v := ⟨_, rfl⟩
      have hv0 : om g0 v = f := by
        rw [← hv, ← om_mul, mul_inv_cancel, map_one]; rfl
      have key : ∀ g : G l, ‖f - om g v‖ = ‖om g⁻¹ f - v‖ := fun g => by
        rw [← LinearIsometryEquiv.norm_map (om g) (om g⁻¹ f - v), map_sub, ← om_mul, mul_inv_cancel, map_one]
        rfl
      have hc : Continuous fun g : G l => ‖f - om g v‖ := (continuous_const.sub (continuous_om v)).norm
      have h0 := hc.tendsto g0
      rw [hv0, sub_self, norm_zero] at h0
      rw [hv]
      exact h0.congr key⟩
  exact { toContinuousMul := hm, toContinuousInv := hi }
end CompanionTheory.ThKR.Mp
