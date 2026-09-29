-- Prove2me | solution 1 for BookProof.QgHermiteCore.hasDerivAt_gaussPoly
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:22:23.687549+00:00
-- url     : https://prove2.me/submissions/73bc75b1-1bf1-44c6-a595-8e977d3bdb8c

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.Ring
set_option autoImplicit false

theorem solution (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => p.eval x * Real.exp (-x ^ 2 / 4))
      ((p.derivative - Polynomial.C (1 / 2) * Polynomial.X * p).eval x *
        Real.exp (-x ^ 2 / 4)) x := by
  have h := (p.hasDerivAt x).mul ((((hasDerivAt_pow 2 x).neg).div_const 4).exp)
  convert h using 1 <;> first | rfl | (simp; ring)
#print axioms solution
