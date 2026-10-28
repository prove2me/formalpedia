-- Prove2me | solution 1 for D1Bound5.bennett_factorial_mul_abs_choose
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:41:59.588818+00:00
-- url     : https://prove2.me/submissions/97096a48-28ef-4554-8a03-94439973fad7

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

section
open Polynomial

namespace D1Bound5





/-- Absolute generalized choose coefficients retain the ordinary factorial
denominator and the actual descending Pochhammer numerator. -/
theorem _root_.solution (r : ℝ) (n : ℕ) :
    (n.factorial : ℝ) * |Ring.choose r n| = |(descPochhammer ℝ n).eval r| := by
  have heq : (descPochhammer ℤ n).smeval r = (descPochhammer ℝ n).eval r := by
    rw [descPochhammer_smeval_eq_ascPochhammer, ascPochhammer_smeval_eq_eval,
      descPochhammer_eval_eq_ascPochhammer]
  have h := Ring.descPochhammer_eq_factorial_smul_choose r n
  rw [heq, nsmul_eq_mul] at h
  have ha := congrArg abs h
  have hfacabs : |(n.factorial : ℝ)| = (n.factorial : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg n.factorial)
  rw [abs_mul, hfacabs] at ha
  exact ha.symm









end D1Bound5
end
