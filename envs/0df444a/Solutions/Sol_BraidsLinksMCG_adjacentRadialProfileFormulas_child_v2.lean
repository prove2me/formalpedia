-- Prove2me | solution 1 for BraidsLinksMCG.adjacentRadialProfileFormulas_child_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T22:52:42.908442+00:00
-- url     : https://prove2.me/submissions/7cdb2033-a619-4f2e-a3a5-172db51ddceb

import Mathlib

theorem solution (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((t ≤ 1 / 2 → max (1 - t) (max (1 / 2) (2 * t - 1)) = 1 - t) ∧
      (1 / 2 ≤ t → t ≤ 3 / 4 → max (1 - t) (max (1 / 2) (2 * t - 1)) = 1 / 2) ∧
      (3 / 4 ≤ t → max (1 - t) (max (1 / 2) (2 * t - 1)) = 2 * t - 1)) ∧
    ((t ≤ 1 / 2 → max 0 (min 1 (4 * t - 2)) = 0) ∧
      (1 / 2 ≤ t → t ≤ 3 / 4 → max 0 (min 1 (4 * t - 2)) = 4 * t - 2) ∧
      (3 / 4 ≤ t → max 0 (min 1 (4 * t - 2)) = 1)) := by
  constructor
  · constructor
    · intro ht
      have hi : 2 * t - 1 ≤ 1 / 2 := by linarith
      have ho : 1 / 2 ≤ 1 - t := by linarith
      rw [max_eq_left hi]
      rw [max_eq_left ho]
    · constructor
      · intro ht0' ht1'
        have hi : 2 * t - 1 ≤ 1 / 2 := by linarith
        have ho : 1 - t ≤ 1 / 2 := by linarith
        rw [max_eq_left hi, max_eq_right ho]
      · intro ht
        have hi : 1 / 2 ≤ 2 * t - 1 := by linarith
        have ho : 1 - t ≤ 2 * t - 1 := by linarith
        rw [max_eq_right hi, max_eq_right ho]
  · constructor
    · intro ht
      have hx : 4 * t - 2 ≤ 0 := by linarith
      have hy : 4 * t - 2 ≤ 1 := by linarith
      rw [min_eq_right hy, max_eq_left hx]
    · constructor
      · intro ht0' ht1'
        have hx : 0 ≤ 4 * t - 2 := by linarith
        have hy : 4 * t - 2 ≤ 1 := by linarith
        rw [min_eq_right hy, max_eq_right hx]
      · intro ht
        have hx : 1 ≤ 4 * t - 2 := by linarith
        rw [min_eq_left hx, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
