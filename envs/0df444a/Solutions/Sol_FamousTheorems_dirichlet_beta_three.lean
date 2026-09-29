-- Prove2me | solution 1 for FamousTheorems.dirichlet_beta_three
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:22:25.570656+00:00
-- url     : https://prove2.me/submissions/d538201e-493d-449d-9dd6-32eb119e0aab

import Mathlib

theorem solution : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 3 * Real.sin (Real.pi * n / 2)) (Real.pi ^ 3 / 32) :=
  hasSum_L_function_mod_four_eval_three
