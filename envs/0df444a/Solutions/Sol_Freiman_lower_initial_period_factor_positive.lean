-- Prove2me | solution 1 for Freiman.lower_initial_period_factor_positive
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T00:21:24.978571+00:00
-- url     : https://prove2.me/submissions/9d416184-b0f7-49a0-aa7f-63cc3ad9fae2

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

theorem solution (x : ℝ) (hx : 0 ≤ x) (hb : x < 43-2*Real.sqrt 462) : 0 < x^2-86*x+1 := by
  have hs0 : 0 ≤ Real.sqrt 462 := Real.sqrt_nonneg _
  have hs : Real.sqrt 462 ^ 2 = 462 := Real.sq_sqrt (by norm_num)
  have h1 : 0 < 43 - 2*Real.sqrt 462 - x := by linarith
  have h2 : 0 < 43 + 2*Real.sqrt 462 - x := by linarith
  nlinarith [mul_pos h1 h2, hs]
