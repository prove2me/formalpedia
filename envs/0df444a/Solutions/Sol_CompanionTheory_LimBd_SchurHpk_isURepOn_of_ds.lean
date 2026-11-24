-- Prove2me | solution 1 for CompanionTheory.LimBd.SchurHpk.isURepOn_of_ds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:21:25.796368+00:00
-- url     : https://prove2.me/submissions/d6f7ed47-8054-4489-ad53-a83551a3b487

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_forth_mul
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
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.SchurHpk
open MeasureTheory Matrix Topology PI.UpqRep CompanionTheory.LimBd.URep
open scoped InnerProductSpace ENNReal
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
omit [CompleteSpace H]
namespace CompanionTheory.LimBd.SchurHpk
theorem _root_.solution {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (h : IsDSHpk k r ε lam σ) :
    IsURepOn (UH (Hpk k r)) σ := by
  obtain ⟨P, ⟨hP, -⟩, -, -, ⟨⟨h1, hm⟩, hn, hc⟩, -⟩ := h
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun x hx v => ?_, fun v => ?_⟩
  · simpa [inv_mul_P hP] using h1
  · have := hm _ (forth_mem hP ha) _ (forth_mem hP hb)
    simp only [← forth_mul hP, back_forth hP] at this
    exact this
  · have := hn _ (forth_mem hP hx) v
    simpa only [back_forth hP] using this
  · have := (hc v).comp (f := fun x => P * x * P⁻¹) (s := UH (Hpk k r))
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).continuousOn
      (fun x hx => forth_mem hP hx)
    simpa only [Function.comp_def, back_forth hP] using this
end CompanionTheory.LimBd.SchurHpk
