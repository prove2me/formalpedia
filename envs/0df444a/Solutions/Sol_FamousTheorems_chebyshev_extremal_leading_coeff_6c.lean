-- Prove2me | solution 1 for FamousTheorems.chebyshev_extremal_leading_coeff_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:46:12.265278+00:00
-- url     : https://prove2.me/submissions/cb95ef28-42c2-49a8-b878-d84387b29d12

import Mathlib

theorem solution {n : ℕ} {P : Polynomial ℝ} (hPdeg : P.degree ≤ n)
    (hPbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) : P.leadingCoeff ≤ 2 ^ (n - 1) :=
  Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one hPdeg hPbnd
