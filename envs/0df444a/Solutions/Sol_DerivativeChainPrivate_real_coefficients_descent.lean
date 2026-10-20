-- Prove2me | solution 1 for DerivativeChainPrivate.real_coefficients_descent
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T01:48:06.333011+00:00
-- url     : https://prove2.me/submissions/571af9de-87c8-4237-bbdd-ed505e2d2b6a

import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false

theorem solution (p : Polynomial ℂ) (hp : ∀ k, (p.coeff k).im = 0) :
    ∃ q : Polynomial ℝ, q.map Complex.ofRealHom = p := by
  let q : Polynomial ℝ := p.sum fun k z => Polynomial.monomial k z.re
  refine ⟨q, ?_⟩
  have hreal (k : ℕ) : (Complex.ofRealHom ((p.coeff k).re)) = p.coeff k := by
    apply Complex.ext
    · simp
    · simpa using (hp k).symm
  simpa only [q, Polynomial.sum, Polynomial.map_sum,
    Polynomial.map_monomial, hreal] using p.sum_monomial_eq
