-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_tent_pointwise_convolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:50:24.45576+00:00
-- url     : https://prove2.me/submissions/ae5eae53-6d8b-4258-a3a4-dc6ab2d5e8cf

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral

/-- At every reserve, the reflected Taylor tent is exactly a convolution. -/
theorem solution
    (F : ℝ → ℝ) (x r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.convolution
      ((Ioc (0 : ℝ) r).indicator (fun t => r - t)) F
      (ContinuousLinearMap.mul ℝ ℝ) volume x =
        ∫ t in (0 : ℝ)..r, (r - t) * F (x - t) := by
  change (∫ t : ℝ,
    (Ioc (0 : ℝ) r).indicator (fun s => r - s) t * F (x - t)) = _
  have hpoint :
      (fun t : ℝ =>
        (Ioc (0 : ℝ) r).indicator (fun s => r - s) t * F (x - t)) =
      (Ioc (0 : ℝ) r).indicator (fun t => (r - t) * F (x - t)) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) r
    · simp [Set.indicator, ht]
    · simp [Set.indicator, ht]
  rw [hpoint, MeasureTheory.integral_indicator measurableSet_Ioc]
  exact (intervalIntegral.integral_of_le hr).symm
