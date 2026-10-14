-- Prove2me | solution 1 for DbarRegularity.eLpNorm_integral_mul_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T15:04:01.021297+00:00
-- url     : https://prove2.me/submissions/be560f8c-3e0b-418c-9bcd-fa77f7b41318

import Theorems.Thm_DbarRegularity_lintegral_sq_lintegral_mul_le
import Mathlib.MeasureTheory.Integral.Prod



namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- `‖∫ h(· - y) f(y) dy‖_{L²} ≤ ‖h‖_{L²} ‖f‖_{L¹}`. -/
theorem eLpNorm_integral_mul_sub_le {d : ℕ} (h f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hh : AEStronglyMeasurable h volume) (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun x => ∫ y, h (x - y) * f y) 2 volume ≤ eLpNorm h 2 volume * eLpNorm f 1 volume := by
  have H := lintegral_sq_lintegral_mul_le h f hh hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_one_eq_lintegral_enorm]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hpt : ∀ x, ‖∫ y, h (x - y) * f y‖ₑ ^ 2 ≤ (∫⁻ y, ‖h (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 := by
    intro x
    gcongr
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp [enorm_mul]
  calc (∫⁻ x, ‖∫ y, h (x - y) * f y‖ₑ ^ 2) ^ (1 / 2 : ℝ)
      ≤ ((∫⁻ x, ‖h x‖ₑ ^ 2) * (∫⁻ y, ‖f y‖ₑ) ^ 2) ^ (1 / 2 : ℝ) := by
        gcongr; exact (lintegral_mono hpt).trans H
    _ = (∫⁻ x, ‖h x‖ₑ ^ 2) ^ (1 / 2 : ℝ) * ∫⁻ y, ‖f y‖ₑ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal

theorem solution {d : ℕ} (h f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hh : AEStronglyMeasurable h volume) (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun x => ∫ y, h (x - y) * f y) 2 volume ≤ eLpNorm h 2 volume * eLpNorm f 1 volume :=
  eLpNorm_integral_mul_sub_le h f hh hf
