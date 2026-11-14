-- Prove2me | solution 1 for ConsistentSubmodular.high_anchor_cubic_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:27.596999+00:00
-- url     : https://prove2.me/submissions/60d06872-2fad-45e5-bd80-03dd6487b7ef

import Mathlib

section

theorem solution (p : ℝ) (hp : 0 ≤ p) (hp9 : p ≤ 9 / 40) :
    6 * p ^ 3 - 13 * p ^ 2 + 7 * p - 1 ≤ 0 := by
  let t := 40 * p / 9
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hs : 0 ≤ 1 - t := by dsimp [t]; linarith
  have hid : 6 * p ^ 3 - 13 * p ^ 2 + 7 * p - 1 =
      -((1 - t) ^ 3 + (57 / 40 : ℝ) * t * (1 - t) ^ 2 +
        (813 / 1600 : ℝ) * t ^ 2 * (1 - t) + (473 / 32000 : ℝ) * t ^ 3) := by
    dsimp [t]
    ring
  rw [hid]
  have : 0 ≤ (1 - t) ^ 3 + (57 / 40 : ℝ) * t * (1 - t) ^ 2 +
      (813 / 1600 : ℝ) * t ^ 2 * (1 - t) + (473 / 32000 : ℝ) * t ^ 3 := by positivity
  linarith

end
