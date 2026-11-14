-- Prove2me | solution 1 for ConsistentSubmodular.middle_child_deficit_second
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:43.695767+00:00
-- url     : https://prove2.me/submissions/c7ba981d-d5ba-44b8-94e9-dbd908271fbd

import Mathlib

section

theorem solution (q d p δ : ℝ)
    (hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hδ : 0 ≤ δ)
    (hpl : (3 : ℝ) / 10 ≤ p) (hpu : p ≤ 1 / 2)
    (hJ : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ) : 1 / 8 + p / 4 ≤ d := by
  have hcoef : 0 < 36 - 25 * q + 3 * q ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 4 - 3 * q by linarith) (show 0 ≤ 7 - q by linarith)]
  have hlo : (36 - 25 * q + 3 * q ^ 2) * (1 / 5) -
      (3 - q) * (3 - 2 * q) - q * (4 - q) * (3 / 10) ≤ 0 := by
    nlinarith [sq_nonneg (q - 14 / 11)]
  have hhi : (36 - 25 * q + 3 * q ^ 2) * (1 / 4) -
      (3 - q) * (3 - 2 * q) - q * (4 - q) * (1 / 2) ≤ 0 := by
    have := mul_nonneg (show 0 ≤ q by linarith) (sub_nonneg.mpr hq1)
    nlinarith only [this]
  have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hpu) hlo
  have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hpl) hhi
  have hline : (36 - 25 * q + 3 * q ^ 2) * (1 / 8 + p / 4) -
      (3 - q) * (3 - 2 * q) - q * (4 - q) * p ≤ 0 := by
    nlinarith only [h1, h2]
  have hδterm := mul_nonneg (sq_nonneg q) hδ
  have hprod : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * (d - (1 / 8 + p / 4)) := by
    nlinarith only [hJ, hline, hδterm]
  have := nonneg_of_mul_nonneg_right hprod hcoef
  linarith

end
