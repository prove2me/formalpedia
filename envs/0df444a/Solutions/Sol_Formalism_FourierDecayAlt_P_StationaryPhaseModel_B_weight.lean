-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:57.886116+00:00
-- url     : https://prove2.me/submissions/dbd03889-2050-4ee6-9a18-8cb5fd446bf5

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_isAddHaar_muPi
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_finrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d : ℕ) (β : ℂ) (hβ : β ≠ 0) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ σ : ℝ, 0 < σ →
    Integrable (fun x : Fin d → ℂ => wt σ x ^ (-(2 * (d : ℤ) + 2))) (muPi β (Fin d)) ∧
    ∫ x : Fin d → ℂ, wt σ x ^ (-(2 * (d : ℤ) + 2)) ∂(muPi β (Fin d)) ≤ C₀ / σ ^ 2 := by
  have := isAddHaar_muPi d β hβ
  have hI : Integrable (fun x : Fin d → ℂ => (1 + ‖x‖) ^ (-(2 * (d : ℤ) + 2))) (muPi β (Fin d)) := by
    have h := integrable_one_add_norm (E := Fin d → ℂ) (μ := muPi β (Fin d)) (r := ((2 * (d : ℤ) + 2 : ℤ) : ℝ))
      (by rw [B_finrank]; push_cast; linarith)
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  refine ⟨∫ x : Fin d → ℂ, (1 + ‖x‖) ^ (-(2 * (d : ℤ) + 2)) ∂(muPi β (Fin d)),
    integral_nonneg fun x => by positivity, fun σ hσ => ?_⟩
  have hEq : (fun x : Fin d → ℂ => wt σ x ^ (-(2 * (d : ℤ) + 2))) =
      fun x => σ ^ (-(2 * (d : ℤ) + 2)) * (fun y : Fin d → ℂ => (1 + ‖y‖) ^ (-(2 * (d : ℤ) + 2))) (σ⁻¹ • x) := by
    funext x
    simp only [wt]
    rw [← mul_zpow, norm_smul, norm_inv, Real.norm_of_nonneg hσ.le]
    congr 1
    field_simp
    ring
  constructor
  · rw [hEq]
    exact (hI.comp_smul (inv_ne_zero hσ.ne')).const_mul _
  · have hsc := Measure.integral_comp_inv_smul (muPi β (Fin d))
      (fun y : Fin d → ℂ => (1 + ‖y‖) ^ (-(2 * (d : ℤ) + 2))) σ
    rw [hEq, integral_const_mul, hsc, B_finrank, abs_of_pos (by positivity), smul_eq_mul,
      ← mul_assoc]
    apply le_of_eq
    rw [div_eq_mul_inv, mul_comm]
    congr 1
    rw [zpow_neg, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_neg, ← zpow_add₀ hσ.ne']
    congr 1
    push_cast
    ring
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
