-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_finitecap_raw_w_overshoot_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:06:36.304611+00:00
-- url     : https://prove2.me/submissions/80e3c18b-a07b-403f-96df-a47adf0d866d

import Mathlib.Analysis.Real.Sqrt

theorem solution
    (d r : ℝ) (hd : 0 ≤ d) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    let w : ℝ → ℝ := fun z =>
      if z ≤ 1 then z else 1 - Real.sqrt (z - 1)
    d + w (1 - r) - w (1 - r + d)
      = max (d - r) 0 + Real.sqrt (max (d - r) 0)  := by
  dsimp
  have hy : 1 - r ≤ (1 : ℝ) := by linarith
  by_cases h : d ≤ r
  · have hz : 1 - r + d ≤ (1 : ℝ) := by linarith
    have hm : max (d - r) (0 : ℝ) = 0 := max_eq_right (by linarith)
    simp only [if_pos hy, if_pos hz, hm, Real.sqrt_zero, add_zero]
    ring
  · have hz : ¬ (1 - r + d ≤ (1 : ℝ)) := by linarith
    have hm : max (d - r) (0 : ℝ) = d - r := max_eq_left (by linarith)
    simp only [if_pos hy, if_neg hz, hm]
    have heq : (1 - r + d) - 1 = d - r := by ring
    rw [heq]
    ring
