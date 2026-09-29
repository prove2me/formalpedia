-- Prove2me | solution 1 for FamousTheorems.landau_inequality_mahler_measure
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:38:12.956984+00:00
-- url     : https://prove2.me/submissions/6c4de6fc-f6c6-4e66-97f7-1a594d638cc6

import Mathlib

theorem solution (p : Polynomial ℂ) :
    p.mahlerMeasure ≤ Real.sqrt (∑ i ∈ p.support, ‖p.coeff i‖ ^ 2) :=
  Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff p
