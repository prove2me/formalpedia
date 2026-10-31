-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_tent_kernel_quadratic_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:47:07.028644+00:00
-- url     : https://prove2.me/submissions/caa72d28-c5e4-4075-8da8-55a6f0360d44

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory intervalIntegral

/-- The triangular small-jump Taylor convolution kernel has quadratic mass. -/
theorem solution
    (r : ℝ) (hr : 0 ≤ r) :
    (∫ t : ℝ, (Ioc (0 : ℝ) r).indicator (fun t => r - t) t) =
      r ^ 2 / 2 := by
  have hcalc : (∫ t in (0 : ℝ)..r, r - t) = r ^ 2 / 2 := by
    calc
      _ = (∫ t in (0 : ℝ)..r, r) - (∫ t in (0 : ℝ)..r, t) := by
        simpa only [id_eq] using (intervalIntegral.integral_sub
          (f := fun _ : ℝ => r) (g := id) intervalIntegrable_const
          (continuous_id.intervalIntegrable _ _))
      _ = r ^ 2 / 2 := by
        rw [intervalIntegral.integral_const, integral_id]
        ring
  rw [MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [← intervalIntegral.integral_of_le hr]
  exact hcalc
