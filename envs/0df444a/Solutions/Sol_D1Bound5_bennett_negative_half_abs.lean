-- Prove2me | solution 1 for D1Bound5.bennett_negative_half_abs
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:14.110028+00:00
-- url     : https://prove2.me/submissions/d0503334-2d74-4cac-a11b-95529247b867

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Theorems.Thm_D1Bound5_bennett_ascPochhammer_half_pos
import Theorems.Thm_D1Bound5_bennett_factorial_mul_abs_choose

section
open Polynomial

namespace D1Bound5









/-- The absolute negative-half tail is the same positive ascending product. -/
theorem _root_.solution (m : ℕ) :
    (m.factorial : ℝ) * |Ring.choose (-1 / 2 : ℝ) m| =
      (ascPochhammer ℝ m).eval (1 / 2) := by
  rw [bennett_factorial_mul_abs_choose]
  have h := ascPochhammer_eval_neg_eq_descPochhammer ℝ (-1 / 2 : ℝ) m
  have ha := congrArg abs h
  norm_num only [neg_div, neg_neg] at ha
  rw [abs_of_pos (bennett_ascPochhammer_half_pos m), abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul] at ha
  simpa only [neg_div] using ha.symm





end D1Bound5
end
