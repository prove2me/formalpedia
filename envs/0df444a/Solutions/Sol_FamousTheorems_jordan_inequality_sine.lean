-- Prove2me | solution 1 for FamousTheorems.jordan_inequality_sine
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:34:31.001999+00:00
-- url     : https://prove2.me/submissions/e3aa7a0e-2e50-4d7e-a071-d04873e5e2b1

import Mathlib

theorem solution {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ Real.pi / 2) :
    2 / Real.pi * x ≤ Real.sin x :=
  Real.mul_le_sin hx hx'
