-- Prove2me | solution 1 for FamousTheorems.hasSum_zeta_two
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:52:36.903254+00:00
-- url     : https://prove2.me/submissions/fea66141-9b71-48b5-91d3-54d7a0119d01

import Mathlib

theorem solution : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) :=
  hasSum_zeta_two
