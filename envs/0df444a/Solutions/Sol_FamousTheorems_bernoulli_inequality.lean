-- Prove2me | solution 1 for FamousTheorems.bernoulli_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:16:06.869344+00:00
-- url     : https://prove2.me/submissions/7ae0e11a-ffbc-48b0-ade7-8dd7b4564431

import Mathlib

theorem solution {a : ℝ} (H : -2 ≤ a) (n : ℕ) : 1 + (n : ℝ) * a ≤ (1 + a) ^ n :=
  one_add_mul_le_pow H n
