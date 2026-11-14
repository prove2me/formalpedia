-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB310_translated_inverse_sqrt_cell_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:07:28.428547+00:00
-- url     : https://prove2.me/submissions/a7256a4d-fc7a-4f4e-944d-0acf62d243f4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- The translated inverse-square-root Gaussian kernel is integrable on a finite positive-width physical cell. -/
theorem solution (s δ : ℝ) (hδ : 0 ≤ δ) :
    IntegrableOn (fun t : ℝ => (t - s) ^ (-(1 / 2 : ℝ)))
      (Set.Ioc s (s + δ)) volume := by
  have hbase : IntervalIntegrable
      (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 δ :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hshift : IntervalIntegrable
      (fun t : ℝ => (t - s) ^ (-(1 / 2 : ℝ)))
      volume (0 + s) (δ + s) :=
    hbase.comp_sub_right s
  have hinterval : IntervalIntegrable
      (fun t : ℝ => (t - s) ^ (-(1 / 2 : ℝ)))
      volume s (s + δ) := by
    simpa only [zero_add, add_comm δ s] using hshift
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by linarith : s ≤ s + δ)).mp hinterval
