-- Prove2me | solution 1 for FamousTheorems.gamma_nat_eq_factorial_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:25:41.680789+00:00
-- url     : https://prove2.me/submissions/962f6cc3-4f56-4930-a4bc-a99f6076b49f

import Mathlib

theorem solution (n : ℕ) : Real.Gamma (n + 1) = n.factorial :=
  Real.Gamma_nat_eq_factorial n
