-- Prove2me | solution 1 for D1Bound5.bennett_Gamma_half_add_nat
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:38:40.495926+00:00
-- url     : https://prove2.me/submissions/01457e93-578d-49e9-894c-b4eab2572788

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

section
open Polynomial

namespace D1Bound5

/-- Positive half-integer Gamma values expressed by the actual ascending
Pochhammer polynomial. Only Gamma's proved recurrence is used. -/
theorem _root_.solution (n : ℕ) :
    Real.Gamma ((1 / 2 : ℝ) + n) =
      Real.Gamma (1 / 2 : ℝ) * (ascPochhammer ℝ n).eval (1 / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have harg : (1 / 2 : ℝ) + (n + 1 : ℕ) = ((1 / 2 : ℝ) + n) + 1 := by
        push_cast
        ring
      rw [harg, Real.Gamma_add_one (show (1 / 2 : ℝ) + n ≠ 0 by positivity),
        ih, ascPochhammer_succ_right]
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_natCast]
      ring













end D1Bound5
end
