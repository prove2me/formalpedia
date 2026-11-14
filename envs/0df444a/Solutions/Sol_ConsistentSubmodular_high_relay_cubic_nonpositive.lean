-- Prove2me | solution 1 for ConsistentSubmodular.high_relay_cubic_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:25.91413+00:00
-- url     : https://prove2.me/submissions/9c46721a-638d-4924-891d-94b7337ba4c3

import Mathlib

section

theorem solution (p : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) :
    17 * p ^ 3 - 41 * p ^ 2 + 20 * p - 3 ≤ 0 := by
  by_cases hquarter : p ≤ 1 / 4
  · have ht : 0 ≤ 4 * p := by positivity
    have hs : 0 ≤ 1 - 4 * p := by linarith
    have hid : 17 * p ^ 3 - 41 * p ^ 2 + 20 * p - 3 =
        -(3 * (1 - 4 * p) ^ 3 + 4 * (4 * p) * (1 - 4 * p) ^ 2 +
          (25 / 16 : ℝ) * (4 * p) ^ 2 * (1 - 4 * p) +
          (19 / 64 : ℝ) * (4 * p) ^ 3) := by ring
    rw [hid]
    have : 0 ≤ 3 * (1 - 4 * p) ^ 3 + 4 * (4 * p) * (1 - 4 * p) ^ 2 +
        (25 / 16 : ℝ) * (4 * p) ^ 2 * (1 - 4 * p) +
        (19 / 64 : ℝ) * (4 * p) ^ 3 := by positivity
    linarith
  · have ht : 0 ≤ 4 * p - 1 := by linarith
    have hs : 0 ≤ 2 - 4 * p := by linarith
    have hid : 17 * p ^ 3 - 41 * p ^ 2 + 20 * p - 3 =
        -((19 / 64 : ℝ) * (2 - 4 * p) ^ 3 +
          (7 / 32 : ℝ) * (4 * p - 1) * (2 - 4 * p) ^ 2 +
          (21 / 16 : ℝ) * (4 * p - 1) ^ 2 * (2 - 4 * p) +
          (9 / 8 : ℝ) * (4 * p - 1) ^ 3) := by ring
    rw [hid]
    have : 0 ≤ (19 / 64 : ℝ) * (2 - 4 * p) ^ 3 +
        (7 / 32 : ℝ) * (4 * p - 1) * (2 - 4 * p) ^ 2 +
        (21 / 16 : ℝ) * (4 * p - 1) ^ 2 * (2 - 4 * p) +
        (9 / 8 : ℝ) * (4 * p - 1) ^ 3 := by positivity
    linarith

end
