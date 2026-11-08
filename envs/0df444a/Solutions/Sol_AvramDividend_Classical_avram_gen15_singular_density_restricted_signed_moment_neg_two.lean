-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen15_singular_density_restricted_signed_moment_neg_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:31:11.429787+00:00
-- url     : https://prove2.me/submissions/0737f728-9be8-49e6-a9e4-d2b71f0913c8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_density_restrict_integral
import Theorems.Thm_AvramDividend_Classical_avram_gen15_singular_density_signed_jump_mean_eq_neg_two
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- The source drift uses precisely the restricted negative jump integral. -/
theorem solution :
    (∫ z in Ioo (-1 : ℝ) 0, z ∂
      (volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) = -2 := by
  let ν : Measure ℝ := volume.withDensity (fun z : ℝ =>
    if z ∈ Ioo (-1 : ℝ) 0
    then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)
  change (∫ z in Ioo (-1 : ℝ) 0, z ∂ν) = -2
  calc
    (∫ z in Ioo (-1 : ℝ) 0, z ∂ν) =
      (∫ z : ℝ, (Ioo (-1 : ℝ) 0).indicator (fun z : ℝ => z) z ∂ν) := by
        rw [integral_indicator measurableSet_Ioo]
    _ = (∫ z in Ioo (-1 : ℝ) 0,
          |z| ^ (-(3 / 2 : ℝ)) *
            (Ioo (-1 : ℝ) 0).indicator (fun z : ℝ => z) z ∂volume) := by
        simpa only [ν] using
          (avram_gen14_singular_density_restrict_integral
            (fun z : ℝ => (Ioo (-1 : ℝ) 0).indicator (fun z : ℝ => z) z))
    _ = (∫ z in Ioo (-1 : ℝ) 0,
          |z| ^ (-(3 / 2 : ℝ)) * z ∂volume) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro z hz
        change |z| ^ (-(3 / 2 : ℝ)) *
          (Ioo (-1 : ℝ) 0).indicator (fun z : ℝ => z) z =
            |z| ^ (-(3 / 2 : ℝ)) * z
        rw [Set.indicator_of_mem hz]
    _ = (∫ z : ℝ, z ∂ν) := by
        simpa only [ν] using
          (avram_gen14_singular_density_restrict_integral (fun z : ℝ => z)).symm
    _ = -2 := by
        simpa only [ν] using
          avram_gen15_singular_density_signed_jump_mean_eq_neg_two
