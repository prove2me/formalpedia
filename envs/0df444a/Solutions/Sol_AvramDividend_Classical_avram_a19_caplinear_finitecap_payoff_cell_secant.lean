-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_caplinear_finitecap_payoff_cell_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:50:46.67771+00:00
-- url     : https://prove2.me/submissions/06741a68-b695-4ce7-8239-df3aaef67137

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-- Cap-linear continuation preserves the interior one-sided dividend slope for a prepayment overshoot. -/
theorem solution
    (w : ℝ → ℝ) (C y d : ℝ) (hy : y ≤ C) (hd : 0 ≤ d)
    (hSlope : ∀ z : ℝ, y ≤ z → z ≤ C →
      z - y ≤ w z - w y) :
    let V : ℝ → ℝ := fun z => if z ≤ C then w z else w C + (z - C)
    d ≤ V (y + d) - w y  := by
  change d ≤
    (if y + d ≤ C then w (y + d) else w C + (y + d - C)) - w y
  by_cases hUpper : y + d ≤ C
  · simp only [if_pos hUpper]
    have hs := hSlope (y + d) (by linarith) hUpper
    linarith
  · simp only [if_neg hUpper]
    have hs := hSlope C hy le_rfl
    linarith
