-- Prove2me | solution 1 for FamousTheorems.hessenberg_cardinal_mul_self_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:55:01.981553+00:00
-- url     : https://prove2.me/submissions/1fa13391-1cf7-4728-9486-6a1b2c4e32ac

import Mathlib

theorem solution {c : Cardinal} (hc : Cardinal.aleph0 ≤ c) : c * c = c :=
  Cardinal.mul_eq_self hc
