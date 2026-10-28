-- Prove2me | solution 1 for FunctionalInequalities.L2.eLpNorm_le_eLpNorm_of_integral_sq_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:44.591216+00:00
-- url     : https://prove2.me/submissions/07dd55c8-d77a-4b0d-b5e7-aadacb9593a9

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
open scoped RealInnerProductSpace
section Comparison
/-- `∫ u² ≤ ∫ v²` implies `‖u‖₂ ≤ ‖v‖₂` for `u, v ∈ L²`. -/
theorem solution {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u v : α → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (h : ∫ x, u x ^ 2 ∂μ ≤ ∫ x, v x ^ 2 ∂μ) :
    eLpNorm u 2 μ ≤ eLpNorm v 2 μ := by
    have hu_int : Integrable (fun x => u x ^ 2) μ :=
      (memLp_two_iff_integrable_sq hu.1).1 hu
    have hv_int : Integrable (fun x => v x ^ 2) μ :=
      (memLp_two_iff_integrable_sq hv.1).1 hv
    have hu_nonneg : 0 ≤ᵐ[μ] (fun x => u x ^ 2) :=
      Filter.Eventually.of_forall (fun x => sq_nonneg (u x))
    have hv_nonneg : 0 ≤ᵐ[μ] (fun x => v x ^ 2) :=
      Filter.Eventually.of_forall (fun x => sq_nonneg (v x))
    have htwo : (0 : ℝ) ≤ 2 := by norm_num
    have hpoint_u (x : α) :
        ‖u x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (u x ^ 2) := by
      rw [Real.enorm_eq_ofReal_abs]
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) htwo]
      simp [sq_abs]
    have hpoint_v (x : α) :
        ‖v x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (v x ^ 2) := by
      rw [Real.enorm_eq_ofReal_abs]
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) htwo]
      simp [sq_abs]
    have hu_lint :
        (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂μ) =
          ENNReal.ofReal (∫ x, u x ^ 2 ∂μ) := by
      calc
        (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂μ) =
            ∫⁻ x, ENNReal.ofReal (u x ^ 2) ∂μ := by
              simp_rw [hpoint_u]
        _ = ENNReal.ofReal (∫ x, u x ^ 2 ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hu_int hu_nonneg).symm
    have hv_lint :
        (∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) ∂μ) =
          ENNReal.ofReal (∫ x, v x ^ 2 ∂μ) := by
      calc
        (∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) ∂μ) =
            ∫⁻ x, ENNReal.ofReal (v x ^ 2) ∂μ := by
              simp_rw [hpoint_v]
        _ = ENNReal.ofReal (∫ x, v x ^ 2 ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hv_int hv_nonneg).symm
    have hu_norm :
        eLpNorm u 2 μ =
          (ENNReal.ofReal (∫ x, u x ^ 2 ∂μ)) ^ (1 / (2 : ℝ)) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat]
      rw [hu_lint]
    have hv_norm :
        eLpNorm v 2 μ =
          (ENNReal.ofReal (∫ x, v x ^ 2 ∂μ)) ^ (1 / (2 : ℝ)) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat]
      rw [hv_lint]
    rw [hu_norm, hv_norm]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h) (by norm_num)
