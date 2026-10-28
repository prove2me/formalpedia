-- Prove2me | solution 1 for AvramDividend.Classical.hasDerivAt_of_deriv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T20:53:47.591518+00:00
-- url     : https://prove2.me/submissions/8319b49b-20bd-4009-838b-56021e9729c7

import Mathlib

theorem solution {W : ℝ → ℝ} {a : ℝ} (hd : deriv W a ≠ 0) : HasDerivAt W (deriv W a) a := by
  have : DifferentiableAt ℝ W a := by
    by_contra h
    exact hd (deriv_zero_of_not_differentiableAt h)
  exact this.hasDerivAt
