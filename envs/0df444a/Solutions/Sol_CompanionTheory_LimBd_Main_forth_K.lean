-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.forth_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:03:48.190995+00:00
-- url     : https://prove2.me/submissions/b25ae377-efb6-48a9-9f0b-5676f222340e

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
import Theorems.Thm_CompanionTheory_LimBd_Main_inv_unitary
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
theorem _root_.solution (hP : IsCayleyU k r ε P) {x : B.Mat k r}
    (hx : x ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)) : P * x * P⁻¹ ∈ Kset ε := by
  have hu : P * x * P⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ hP.2 hx.2) (inv_unitary hP)
  refine ⟨hu, ?_⟩
  have h1 : (P * x * P⁻¹)ᴴ * Jm ε * (P * x * P⁻¹) = Jm ε := forth_mem hP.1 hx.1
  have h2 : (P * x * P⁻¹) * (P * x * P⁻¹)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hu
  generalize P * x * P⁻¹ = g at h1 h2
  calc g * Jm ε = g * (gᴴ * Jm ε * g) := by rw [h1]
    _ = (g * gᴴ) * Jm ε * g := by simp only [Matrix.mul_assoc]
    _ = Jm ε * g := by rw [h2, Matrix.one_mul]
end CompanionTheory.LimBd.Main
