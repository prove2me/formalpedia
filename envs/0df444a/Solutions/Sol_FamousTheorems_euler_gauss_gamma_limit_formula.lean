-- Prove2me | solution 1 for FamousTheorems.euler_gauss_gamma_limit_formula
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:37:23.152386+00:00
-- url     : https://prove2.me/submissions/36951374-9367-49a3-861c-621754ac9597

import Mathlib

theorem solution (s : ℂ) :
    Filter.Tendsto (fun n : ℕ => (n : ℂ) ^ s * n.factorial / ∏ j ∈ Finset.range (n + 1), (s + j))
      Filter.atTop (nhds (Complex.Gamma s)) :=
  Complex.GammaSeq_tendsto_Gamma s
