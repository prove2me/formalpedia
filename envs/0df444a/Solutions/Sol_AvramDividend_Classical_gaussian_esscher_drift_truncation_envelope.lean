-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_drift_truncation_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:29:29.440815+00:00
-- url     : https://prove2.me/submissions/62a81215-d6ce-4428-82f4-13d65772a993

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_drift_small_quadratic
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_drift_large_uniform

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- Truncated Esscher drift error has the same integrable envelope as a Lévy measure. -/
theorem solution (φ z : ℝ) (hφ : 0 < φ) (hz : 0 ≤ z) :
    |(if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)| ≤
      (φ + 1 / φ) * min (z ^ 2) 1 := by
  have hinv : 0 ≤ 1 / φ := div_nonneg zero_le_one hφ.le
  by_cases hsmall : z ≤ 1
  · have hbound : z ^ 2 ≤ 1 := by
      have hmul : 0 ≤ z * (1 - z) :=
        mul_nonneg hz (by linarith)
      nlinarith
    have hexp : Real.exp (-φ * z) ≤ 1 := by
      have hneg : -φ * z ≤ 0 := by
        nlinarith [mul_nonneg hφ.le hz]
      have hle := (Real.exp_le_exp).mpr hneg
      simpa only [Real.exp_zero] using hle
    have hnonneg : 0 ≤ z - z * Real.exp (-φ * z) := by
      have hmul := mul_le_mul_of_nonneg_left hexp hz
      nlinarith
    have hsmallbound :=
      gaussian_esscher_drift_small_quadratic φ z hφ.le hz
    have hscale : φ * z ^ 2 ≤ (φ + 1 / φ) * z ^ 2 := by
      apply mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg z)
    simp only [if_pos hsmall, min_eq_left hbound, abs_of_nonneg hnonneg]
    linarith
  · have hbig : 1 < z := lt_of_not_ge hsmall
    have hbound : 1 ≤ z ^ 2 := by
      have hmul : 0 ≤ z * (z - 1) :=
        mul_nonneg hz (by linarith)
      nlinarith
    have hnonneg : 0 ≤ z * Real.exp (-φ * z) :=
      mul_nonneg hz (Real.exp_pos _).le
    have hlargebound :=
      gaussian_esscher_drift_large_uniform φ z hφ hz
    simp only [if_neg hsmall, zero_sub, abs_neg,
      abs_of_nonneg hnonneg, min_eq_right hbound, mul_one]
    linarith
