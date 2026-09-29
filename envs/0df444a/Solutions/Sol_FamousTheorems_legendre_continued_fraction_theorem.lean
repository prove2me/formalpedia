-- Prove2me | solution 1 for FamousTheorems.legendre_continued_fraction_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:13:36.736901+00:00
-- url     : https://prove2.me/submissions/b85be4c6-6259-4651-b014-d6cdde795fb4

import Mathlib

theorem solution {ξ : ℝ} {q : ℚ} (h : |ξ - q| < 1 / (2 * (q.den : ℝ) ^ 2)) : ∃ n : ℕ, q = ξ.convergent n :=
  Real.exists_rat_eq_convergent h
