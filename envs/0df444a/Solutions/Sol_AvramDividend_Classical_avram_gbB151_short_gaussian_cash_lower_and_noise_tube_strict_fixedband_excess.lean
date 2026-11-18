-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB151_short_gaussian_cash_lower_and_noise_tube_strict_fixedband_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:15:36.6932+00:00
-- url     : https://prove2.me/submissions/19b43364-7a8e-4f7a-a36f-38b7790efd6c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section
/-- Short-horizon Gaussian cash lower and tube noise give strict source excess. -/
theorem solution
    (y d F N : ℝ)
    (hylo : (249 / 2000 : ℝ) ≤ y)
    (hyhi : y ≤ (1 / 8 : ℝ))
    (hdlo : (173 / 100000 : ℝ) ≤ d)
    (hN : |N| ≤ (1 / 4000 : ℝ))
    (hCash : Real.exp (-(99 / 10000000 : ℝ)) * d +
        Real.exp (-(1 / 100000 : ℝ)) * (2 * y - 4 * y ^ 2) ≤ F) :
    ¬ F - (3 / 16 : ℝ) ≤ N + (1 / 1936 : ℝ) := by
  have hWlo : (186999 / 1000000 : ℝ) ≤
      2 * y - 4 * y ^ 2 := by
    have ha : 0 ≤ y - (249 / 2000 : ℝ) := by linarith
    have hb : 0 ≤ 2 - 4 * (y + (249 / 2000 : ℝ)) := by linarith
    nlinarith [mul_nonneg ha hb]
  have hWnonneg : 0 ≤ 2 * y - 4 * y ^ 2 := by linarith
  have hDnonneg : 0 ≤ d := by linarith
  have hExpS :
      (1 - (99 / 10000000 : ℝ)) ≤
        Real.exp (-(99 / 10000000 : ℝ)) := by
    nlinarith [Real.add_one_le_exp (-(99 / 10000000 : ℝ))]
  have hExpT :
      (1 - (1 / 100000 : ℝ)) ≤
        Real.exp (-(1 / 100000 : ℝ)) := by
    nlinarith [Real.add_one_le_exp (-(1 / 100000 : ℝ))]
  have hCashS :
      (1 - (99 / 10000000 : ℝ)) * d ≤
        Real.exp (-(99 / 10000000 : ℝ)) * d :=
    mul_le_mul_of_nonneg_right hExpS hDnonneg
  have hCashT :
      (1 - (1 / 100000 : ℝ)) * (186999 / 1000000 : ℝ) ≤
        Real.exp (-(1 / 100000 : ℝ)) * (2 * y - 4 * y ^ 2) := by
    calc
      _ ≤ (1 - (1 / 100000 : ℝ)) * (2 * y - 4 * y ^ 2) :=
        mul_le_mul_of_nonneg_left hWlo (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right hExpT hWnonneg
  intro hBound
  have hNup := (abs_le.mp hN).2
  nlinarith [hCashS, hCashT]
