-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_tent_interval_reflection
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:32:17.836318+00:00
-- url     : https://prove2.me/submissions/12ba83df-3df6-42d7-8936-048b3021e476

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory intervalIntegral

/-- Original interior Taylor interval equals its reflected tent convolution integral. -/
theorem solution
    (F : ℝ → ℝ) (x r : ℝ) :
    (∫ u in (x - r)..x, (u - (x - r)) * F u) =
      ∫ s in (0 : ℝ)..r, (r - s) * F (x - s) := by
  have h := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := r)
    (fun u : ℝ => (u - (x - r)) * F u) x
  calc
    (∫ u in (x - r)..x, (u - (x - r)) * F u) =
        ∫ s in (0 : ℝ)..r, (x - s - (x - r)) * F (x - s) := by
      simpa only [sub_zero] using h.symm
    _ = ∫ s in (0 : ℝ)..r, (r - s) * F (x - s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      congr 1
      ring
