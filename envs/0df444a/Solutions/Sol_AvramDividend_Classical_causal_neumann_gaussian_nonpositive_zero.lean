-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_gaussian_nonpositive_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:10:57.05374+00:00
-- url     : https://prove2.me/submissions/e1bab417-7bc1-444a-b464-7961c93941e9

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Every noninitial Gaussian Neumann correction vanishes on nonpositive times. -/
theorem solution
    (a w : ℝ) (P Q : ℕ → ℝ → ℝ)
    (hQsucc : ∀ n : ℕ, Q (n + 1) = fun x : ℝ =>
      (1 / a) * (∫ t in Ioc (0 : ℝ) x,
        Real.exp (w * t) * P n t ∂volume)) :
    ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → Q (n + 1) x = 0 := by
  intro n x hx
  rw [congrFun (hQsucc n) x]
  rw [Ioc_eq_empty_of_le hx]
  simp
