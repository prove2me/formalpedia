-- Prove2me | solution 1 for FamousTheorems.one_add_div_pow_tendsto_exp_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:25:42.745985+00:00
-- url     : https://prove2.me/submissions/03d61ba3-a1b8-4c3b-8e8f-760dfd614bab

import Mathlib

theorem solution (t : ℝ) : Filter.Tendsto (fun n : ℕ => (1 + t / n) ^ n) Filter.atTop (nhds (Real.exp t)) :=
  Real.tendsto_one_add_div_pow_exp t
