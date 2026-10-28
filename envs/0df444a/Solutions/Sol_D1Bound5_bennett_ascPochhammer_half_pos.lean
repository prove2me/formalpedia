-- Prove2me | solution 1 for D1Bound5.bennett_ascPochhammer_half_pos
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:39:23.850083+00:00
-- url     : https://prove2.me/submissions/c3de3558-0136-4857-a0e1-154dd640aa5a

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

section
open Polynomial

namespace D1Bound5



theorem _root_.solution (n : ℕ) :
    0 < (ascPochhammer ℝ n).eval (1 / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_right]
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_natCast]
      exact mul_pos ih (by positivity)











end D1Bound5
end
