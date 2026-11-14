-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a117_original_gaussian_true_crossing_HJB_separate_variance_clock_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:15:25.777532+00:00
-- url     : https://prove2.me/submissions/47ee3cbd-1f5a-4075-a960-964e546c6778

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- Actual original Gaussian crossing-cell HJB bounds keep its physical variance correction and generator drift clock distinct. -/
theorem solution
    (A B C z variance clock K : ℝ) (hK : 0 ≤ K)
    (hv : 0 ≤ variance) (hc : 0 ≤ clock)
    (hA : |A| ≤ K) (hB : |B| ≤ K) (hC : |C| ≤ K) :
    |A * z + B * (z^2 - variance) + clock * C| ≤
      K * (|z| + z^2 + variance + clock) := by
  have hvAbs : |z^2 - variance| ≤ z^2 + variance := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg z]
  have h1 : |A * z| ≤ K * |z| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hA (abs_nonneg z)
  have h2 : |B * (z^2 - variance)| ≤ K * (z^2 + variance) := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hB (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hvAbs hK)
  have h3 : |clock * C| ≤ K * clock := by
    rw [abs_mul, abs_of_nonneg hc]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hC hc
  calc
    |A * z + B * (z^2 - variance) + clock * C| ≤
        |A * z| + |B * (z^2 - variance)| + |clock * C| := by
      have ha := abs_add_le (A * z) (B * (z^2 - variance))
      have hb := abs_add_le (A * z + B * (z^2 - variance)) (clock * C)
      linarith
    _ ≤ K * |z| + K * (z^2 + variance) + K * clock := by
      gcongr
    _ = K * (|z| + z^2 + variance + clock) := by ring
