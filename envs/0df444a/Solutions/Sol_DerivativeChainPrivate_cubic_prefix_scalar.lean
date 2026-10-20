-- Prove2me | solution 1 for DerivativeChainPrivate.cubic_prefix_scalar
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T01:57:11.565983+00:00
-- url     : https://prove2.me/submissions/970149ac-a7ba-4366-b5fc-f38c0d3566bb

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

theorem solution (x b : ℝ) :
    (b + Real.sqrt (x ^ 2 + b ^ 2)) ^ 2 ≤ 2 * (x ^ 2 + 2 * b ^ 2) := by
  have hs := Real.sq_sqrt (show 0 ≤ x ^ 2 + b ^ 2 by positivity)
  nlinarith [sq_nonneg (Real.sqrt (x ^ 2 + b ^ 2) - b)]
