-- Prove2me | solution 1 for FamousTheorems.primorial_lt_four_pow_bound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:14:48.188214+00:00
-- url     : https://prove2.me/submissions/f3598afb-0db8-4bb1-9f61-5557086d5d89

import Mathlib

theorem solution (n : ℕ) (hn : n ≠ 0) : primorial n < 4 ^ n :=
  primorial_lt_four_pow n hn
