-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.letter_recursion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:27:50.881598+00:00
-- url     : https://prove2.me/submissions/f34ccf99-25d3-4430-afa2-350cfb3c7395

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
import Theorems.Thm_CompanionTheory_LimBd_Main_kfin_iff
import Theorems.Thm_CompanionTheory_LimBd_Main_isCoef_of_J
import Theorems.Thm_CompanionTheory_LimBd_Main_mem_box_self
import Theorems.Thm_CompanionTheory_LimBd_Main_mem_box_add
import Theorems.Thm_CompanionTheory_LimBd_Main_mem_box_sub
import Theorems.Thm_CompanionTheory_LimBd_Main_mem_spanBox_of_eq
import Theorems.Thm_CompanionTheory_LimBd_Main_dot_transport
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_forth_mem
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : B.Mat k r}
namespace CompanionTheory.LimBd.Main
theorem _root_.solution : LetterStep := by
  intro t hZ hZd k r ε μ h q φ hq hφ hg hlt
  rcases hq with rfl | ⟨x, y, hq⟩
  · rw [one_mul]
    exact Submodule.subset_span ⟨μ, mem_box_self μ, hφ⟩
  have hφ' := hφ
  obtain ⟨H, i1, i2, i3, σ, v, w, hμ, ⟨P, hP, hτ⟩, hv, hw, hφG⟩ := hφ'
  rw [kfin_iff hP] at hv hw
  rcases hq with hq | hq
  · obtain ⟨X⟩ := hZ _ ε μ H _ hμ hτ h hg hlt
    obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := X.toSum v w (P *ᵥ x) (P *ᵥ y) hv hw
    refine mem_spanBox_of_eq hφ (ψ' := ∑ i, fun g => ⟪wI i, X.σs (sI i) (P * g * P⁻¹) (vI i)⟫_ℂ)
      (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, mem_box_add μ (sI i),
        isCoef_of_J hP (X.ds _ (hI i).1).1 (X.ds _ (hI i).1).2 (hI i).2.1 (hI i).2.2⟩) fun g hgG => ?_
    have := hsum _ (forth_mem hP.1 hgG)
    simp only [back_forth hP.1, dot_transport hP] at this
    rw [Pi.mul_apply, hq g hgG, hφG g hgG, mul_comm, this, Finset.sum_apply]
  · obtain ⟨X⟩ := hZd _ ε μ H _ hμ hτ h hg hlt
    obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := X.toSum v w (P *ᵥ x) (P *ᵥ y) hv hw
    refine mem_spanBox_of_eq hφ (ψ' := ∑ i, fun g => ⟪wI i, X.σs (sI i) (P * g * P⁻¹) (vI i)⟫_ℂ)
      (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, mem_box_sub μ (sI i),
        isCoef_of_J hP (X.ds _ (hI i).1).1 (X.ds _ (hI i).1).2 (hI i).2.1 (hI i).2.2⟩) fun g hgG => ?_
    have := hsum _ (forth_mem hP.1 hgG)
    have hi : (P * g * P⁻¹)⁻¹ = P * g⁻¹ * P⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
        Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1.1), Matrix.mul_assoc]
    simp only [back_forth hP.1, hi, dot_transport hP] at this
    rw [Pi.mul_apply, hq g hgG, hφG g hgG, mul_comm, this, Finset.sum_apply]
end CompanionTheory.LimBd.Main
