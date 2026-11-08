-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen14_singular_levy_square_jump_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:02:07.71453+00:00
-- url     : https://prove2.me/submissions/48dc1ff9-04cb-4f6e-b49e-877473ea18da

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_density_restrict_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- The proposed negative Levy density has finite square-jump moment exactly two-thirds. -/
theorem solution :
    (∫ z : ℝ, |z| ^ (2 : ℕ) ∂(volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) = 2 / 3 := by
  rw [avram_gen14_singular_density_restrict_integral]
  calc
    (∫ z in Ioo (-1 : ℝ) 0,
      |z| ^ (-(3 / 2 : ℝ)) * |z| ^ (2 : ℕ) ∂volume) =
      (∫ z in Ioo (-1 : ℝ) 0, |z| ^ (1 / 2 : ℝ) ∂volume) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro z hz
        have hpos : 0 < |z| := abs_pos.mpr (ne_of_lt hz.2)
        change |z| ^ (-(3 / 2 : ℝ)) * |z| ^ (2 : ℕ) = |z| ^ (1 / 2 : ℝ)
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_add hpos]
        congr 1
        norm_num
    _ = (∫ z in (-1 : ℝ)..0, |z| ^ (1 / 2 : ℝ)) := by
        rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0)]
        rw [integral_Ioc_eq_integral_Ioo]
    _ = (∫ r in (0 : ℝ)..1, |(-r)| ^ (1 / 2 : ℝ)) := by
        simpa using (intervalIntegral.integral_comp_neg
          (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun z : ℝ => |z| ^ (1 / 2 : ℝ))).symm
    _ = (∫ r in (0 : ℝ)..1, r ^ (1 / 2 : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hrnonneg : 0 ≤ r :=
          (show r ∈ Icc (0 : ℝ) 1 by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hr).1
        simp [abs_neg, abs_of_nonneg hrnonneg]
    _ = 2 / 3 := by
        rw [integral_rpow (a := (0 : ℝ)) (b := (1 : ℝ))
          (r := (1 / 2 : ℝ)) (by left; norm_num)]
        norm_num
