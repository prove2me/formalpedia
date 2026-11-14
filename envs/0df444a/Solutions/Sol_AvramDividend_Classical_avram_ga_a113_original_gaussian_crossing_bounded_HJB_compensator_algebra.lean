-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a113_original_gaussian_crossing_bounded_HJB_compensator_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:46:22.13537+00:00
-- url     : https://prove2.me/submissions/f95c29da-4329-4b03-99e9-69eff215f45c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- Bounded genuine original Gaussian first/Hessian/generator coefficients control its full physical crossing-cell compensator without extending the spatial value outside the positive reserve domain. -/
theorem solution
    (A B C z v K : ℝ) (hK : 0 ≤ K) (hv : 0 ≤ v)
    (hA : |A| ≤ K) (hB : |B| ≤ K) (hC : |C| ≤ K) :
    |A * z + B * (z^2 - v) + v * C| ≤
      (2 * K) * (|z| + z^2 + v) := by
  have hz : 0 ≤ z^2 := sq_nonneg z
  have hAbsDiff : |z^2 - v| ≤ z^2 + v := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have h1 : |A * z| ≤ K * |z| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hA (abs_nonneg z)
  have h2 : |B * (z^2 - v)| ≤ K * (z^2 + v) := by
    rw [abs_mul]
    calc
      |B| * |z^2 - v| ≤ K * |z^2 - v| :=
        mul_le_mul_of_nonneg_right hB (abs_nonneg _)
      _ ≤ K * (z^2 + v) :=
        mul_le_mul_of_nonneg_left hAbsDiff hK
  have h3 : |v * C| ≤ K * v := by
    rw [abs_mul, abs_of_nonneg hv]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hC hv
  calc
    |A * z + B * (z^2 - v) + v * C| ≤
        |A * z + B * (z^2 - v)| + |v * C| := abs_add_le _ _
    _ ≤ |A * z| + |B * (z^2 - v)| + |v * C| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ K * |z| + K * (z^2 + v) + K * v := by
      gcongr
    _ ≤ (2 * K) * (|z| + z^2 + v) := by
      nlinarith [mul_nonneg hK (abs_nonneg z),
        mul_nonneg hK hz, mul_nonneg hK hv]
