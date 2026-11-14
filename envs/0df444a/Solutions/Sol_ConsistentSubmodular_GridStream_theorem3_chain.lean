-- Prove2me | solution 1 for ConsistentSubmodular.GridStream.theorem3_chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:08.153244+00:00
-- url     : https://prove2.me/submissions/36fe05ba-574d-4c99-8b87-24129ce7b42c

import Mathlib

section

open scoped BigOperators
open Finset

theorem solution {k x j ε : ℝ} (hk : 0 < k) (hx0 : k / 2 ≤ x) (hx1 : x ≤ k / 2 + ε * k)
    (hj : 1 ≤ j) (hε0 : 0 < ε) (hε4 : ε < 1 / 4) (hεk : 1 ≤ ε * k) :
    x * k + (k - x) * (k + j) - x * (k - x) ≤ (3 / 4 + 6 * ε) * (k * (k + j - 1)) := by
  have hd0 : 0 ≤ x - k / 2 := by linarith
  have hsq : (x - k / 2) ^ 2 ≤ (ε * k) ^ 2 := pow_le_pow_left₀ hd0 (by linarith) 2
  have hεkk : 0 ≤ ε * k ^ 2 := mul_nonneg hε0.le (sq_nonneg _)
  have hxj : 0 ≤ (x - k / 2) * j := mul_nonneg hd0 (by linarith)
  have hkj : 0 ≤ k * j := mul_nonneg hk.le (by linarith)
  have hsq2 : 0 ≤ (1 + 2 * ε) ^ 2 - 1 := by nlinarith
  have hkj1 : 0 ≤ k * (k + j - 1) := mul_nonneg hk.le (by linarith)
  calc x * k + (k - x) * (k + j) - x * (k - x)
      = k ^ 2 + k * j - x * j - x * k + x ^ 2 := by ring
    _ ≤ k ^ 2 + k * j - k * j / 2 - k ^ 2 / 2 + (k + 2 * ε * k) ^ 2 / 4 := by
        nlinarith only [hsq, hεkk, hxj]
    _ ≤ 3 / 4 * (k + 2 * ε * k) ^ 2 + 1 / 2 * k * j := by
        nlinarith only [hεkk, sq_nonneg (ε * k)]
    _ ≤ 3 / 4 * (1 + 2 * ε) ^ 2 * (k * (k + j)) := by
        nlinarith only [mul_nonneg hkj hsq2, hkj]
    _ ≤ 3 / 4 * (1 + 2 * ε) ^ 2 * ((1 + ε) * (k * (k + j - 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith only [mul_nonneg (mul_nonneg hε0.le hk.le) (sub_nonneg.mpr hj), hεk, hk]
    _ ≤ (3 / 4 + 6 * ε) * (k * (k + j - 1)) := by
        have hpoly : 3 / 4 * (1 + 2 * ε) ^ 2 * (1 + ε) ≤ 3 / 4 + 6 * ε := by
          nlinarith only [mul_nonneg hε0.le (sub_nonneg.mpr hε4.le),
            mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hε4.le), hε0]
        nlinarith only [mul_le_mul_of_nonneg_right hpoly hkj1]

end
