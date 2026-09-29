-- Prove2me | solution 1 for BookProof.QgHermiteCore.deriv2_gaussPoly
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:23:15.598206+00:00
-- url     : https://prove2.me/submissions/e13e28b2-c8b6-4b8b-bd64-c83c4b55a6e5

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.Ring
set_option autoImplicit false

private theorem gaussian_polynomial_derivative (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => p.eval x * Real.exp (-x ^ 2 / 4))
      ((p.derivative - Polynomial.C (1 / 2) * Polynomial.X * p).eval x *
        Real.exp (-x ^ 2 / 4)) x := by
  have h := (p.hasDerivAt x).mul ((((hasDerivAt_pow 2 x).neg).div_const 4).exp)
  convert h using 1 <;> first | rfl | (simp; ring)


private theorem derivative_formula (p : Polynomial ℝ) :
    deriv (fun x : ℝ => p.eval x * Real.exp (-x ^ 2 / 4)) =
      fun x : ℝ => (p.derivative - Polynomial.C (1 / 2) * Polynomial.X * p).eval x *
        Real.exp (-x ^ 2 / 4) := by
  funext x
  exact (gaussian_polynomial_derivative p x).deriv

theorem solution (p : Polynomial ℝ) :
    deriv (deriv (fun x : ℝ => p.eval x * Real.exp (-x ^ 2 / 4))) =
      fun x : ℝ => ((p.derivative - Polynomial.C (1 / 2) * Polynomial.X * p).derivative -
        Polynomial.C (1 / 2) * Polynomial.X *
          (p.derivative - Polynomial.C (1 / 2) * Polynomial.X * p)).eval x *
        Real.exp (-x ^ 2 / 4) := by
  rw [derivative_formula, derivative_formula]
#print axioms solution
