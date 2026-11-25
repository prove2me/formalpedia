-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.isCoef_of_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:14:45.148294+00:00
-- url     : https://prove2.me/submissions/753c2a48-76c8-494d-a3ab-3b4b0a4f210f

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
import Theorems.Thm_CompanionTheory_LimBd_Main_kfin_iff
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
theorem _root_.solution (hP : IsCayleyU k r ε P) {μ : Fin (2 * r + k + 1) → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {τ : B.Mat k r → (H →L[ℂ] H)} (hμ : IsHCParam μ) (hτ : IsDS ε μ τ)
    {v w : H} (hv : IsKFin ε τ v) (hw : IsKFin ε τ w) :
    IsCoef k r ε μ fun x => ⟪w, τ (P * x * P⁻¹) v⟫_ℂ := by
  have e : (fun g => (fun x => τ (P * x * P⁻¹)) (P⁻¹ * g * P)) = τ := funext fun g => by
    simp only [forth_back hP.1]
  refine ⟨H, _, _, inferInstance, fun x => τ (P * x * P⁻¹), v, w, hμ, ⟨P, hP, by rw [e]; exact hτ⟩, ?_, ?_,
    fun _ _ => rfl⟩
  · rw [kfin_iff hP, e]; exact hv
  · rw [kfin_iff hP, e]; exact hw
end CompanionTheory.LimBd.Main
