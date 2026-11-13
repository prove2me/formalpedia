-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a50_small_drift_large_raw_increment_energy_le_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:13:12.614203+00:00
-- url     : https://prove2.me/submissions/16ebc571-a29f-4745-8d7b-974ed2f161d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- The original Gaussian raw large-cell tail is controlled by the centred tail once deterministic drift is small. -/
theorem solution (z d η : ℝ) (hη : 0 < η)
    (hDrift : |d| ≤ η / 2) :
    (if η ≤ |z + d| then (z + d) ^ 2 else 0) ≤
      4 * (if η / 2 ≤ |z| then z ^ 2 else 0) := by
  by_cases h : η ≤ |z + d|
  · have hCenter : η / 2 ≤ |z| := by
      have hTriangle := abs_add_le z d
      linarith
    simp only [if_pos h, if_pos hCenter]
    have hb : |z + d| ≤ 2 * |z| := by
      have hTriangle := abs_add_le z d
      linarith
    have hnonneg : 0 ≤ 2 * |z| + |z + d| := by positivity
    have hmul := mul_nonneg (sub_nonneg.mpr hb) hnonneg
    nlinarith [sq_abs z, sq_abs (z + d)]
  · simp only [if_neg h]
    by_cases hc : η / 2 ≤ |z|
    · simp only [if_pos hc]
      nlinarith [sq_nonneg z]
    · simp only [if_neg hc]
      norm_num
