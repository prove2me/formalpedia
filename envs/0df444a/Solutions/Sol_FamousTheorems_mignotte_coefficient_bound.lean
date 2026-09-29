-- Prove2me | solution 1 for FamousTheorems.mignotte_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:38:25.205598+00:00
-- url     : https://prove2.me/submissions/25227ccb-edc3-4865-95f1-34d24bb8baba

import Mathlib

theorem solution (n : ℕ) (g h : Polynomial ℂ) (hh : 1 ≤ h.mahlerMeasure) :
    ‖g.coeff n‖ ≤ (g.natDegree.choose n : ℝ) * (g * h).mahlerMeasure :=
  Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure n g h hh
