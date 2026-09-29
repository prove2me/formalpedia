-- Prove2me | solution 1 for FamousTheorems.chebyshev_gauss_quadrature
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:50:31.120039+00:00
-- url     : https://prove2.me/submissions/c3311bc0-37d5-48b2-b9c2-188c5639c422

import Mathlib

open MeasureTheory

theorem solution {n : ℕ} {P : Polynomial ℝ} (hn : n ≠ 0) (hP : P.degree < 2 * n) :
    ∫ x, P.eval x ∂Polynomial.Chebyshev.measureT = Polynomial.Chebyshev.sumZeroes n P :=
  Polynomial.Chebyshev.integral_eq_sumZeroes hn hP
