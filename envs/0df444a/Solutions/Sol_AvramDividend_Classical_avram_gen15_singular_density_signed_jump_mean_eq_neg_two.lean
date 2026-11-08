-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen15_singular_density_signed_jump_mean_eq_neg_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:28:58.355436+00:00
-- url     : https://prove2.me/submissions/f2f3b804-de78-435e-a4fd-fb6df16a7a56

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_density_restrict_integral
import Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_levy_absolute_first_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- The singular Levy density has signed first jump moment negative two. -/
theorem solution :
    (∫ z : ℝ, z ∂(volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) = -2 := by
  let ν : Measure ℝ := volume.withDensity (fun z : ℝ =>
    if z ∈ Ioo (-1 : ℝ) 0
    then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)
  change (∫ z : ℝ, z ∂ν) = -2
  have hpositive : (∫ z : ℝ, |z| ∂ν) = 2 := by
    simpa only [ν] using avram_gen14_singular_levy_absolute_first_moment
  calc
    (∫ z : ℝ, z ∂ν) =
        (∫ z in Ioo (-1 : ℝ) 0, |z| ^ (-(3 / 2 : ℝ)) * z ∂volume) := by
          simpa only [ν] using
            (avram_gen14_singular_density_restrict_integral (fun z : ℝ => z))
    _ = (∫ z in Ioo (-1 : ℝ) 0,
          -( |z| ^ (-(3 / 2 : ℝ)) * |z|) ∂volume) := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro z hz
          change |z| ^ (-(3 / 2 : ℝ)) * z =
            -(|z| ^ (-(3 / 2 : ℝ)) * |z|)
          rw [abs_of_neg hz.2]
          ring
    _ = -(∫ z in Ioo (-1 : ℝ) 0,
          |z| ^ (-(3 / 2 : ℝ)) * |z| ∂volume) := by
          rw [integral_neg]
    _ = -(∫ z : ℝ, |z| ∂ν) := by
          rw [avram_gen14_singular_density_restrict_integral]
    _ = -2 := by rw [hpositive]
