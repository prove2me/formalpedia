-- Prove2me | solution 1 for AvramDividend.Classical.ladder_height_truncated_area_interval_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:52:24.297984+00:00
-- url     : https://prove2.me/submissions/2f6074fa-04b4-4295-88a4-7ce941c214f1

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory intervalIntegral Set

/-- The ladder-height truncated area is no larger than min(z²,z). -/
theorem solution (z : ℝ) (hz : 0 ≤ z) :
    (∫ t in (0 : ℝ)..z, min 1 t) ≤ min (z ^ 2) z := by
  have hcont : Continuous (fun t : ℝ => min 1 t) :=
    continuous_const.min continuous_id
  have hminInt :
      IntervalIntegrable (fun t : ℝ => min 1 t) volume 0 z :=
    hcont.intervalIntegrable 0 z
  have hidInt :
      IntervalIntegrable (fun t : ℝ => t) volume 0 z :=
    continuous_id.intervalIntegrable 0 z
  have honeInt :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 z :=
    continuous_const.intervalIntegrable 0 z
  have hleId :
      (∫ t in (0 : ℝ)..z, min 1 t) ≤
        (∫ t in (0 : ℝ)..z, t) :=
    intervalIntegral.integral_mono_on hz hminInt hidInt
      (by
        intro t ht
        exact min_le_right 1 t)
  have hleOne :
      (∫ t in (0 : ℝ)..z, min 1 t) ≤
        (∫ _ in (0 : ℝ)..z, (1 : ℝ)) :=
    intervalIntegral.integral_mono_on hz hminInt honeInt
      (by
        intro t ht
        exact min_le_left 1 t)
  have hid : (∫ t in (0 : ℝ)..z, t) = z ^ 2 / 2 := by
    simpa using (integral_id (a := (0 : ℝ)) (b := z))
  have hone : (∫ _ in (0 : ℝ)..z, (1 : ℝ)) = z := by
    simp [intervalIntegral.integral_const]
  have hsqBound :
      (∫ t in (0 : ℝ)..z, min 1 t) ≤ z ^ 2 := by
    rw [hid] at hleId
    nlinarith [sq_nonneg z]
  have hlinBound :
      (∫ t in (0 : ℝ)..z, min 1 t) ≤ z := by
    rwa [hone] at hleOne
  exact le_min hsqBound hlinBound
