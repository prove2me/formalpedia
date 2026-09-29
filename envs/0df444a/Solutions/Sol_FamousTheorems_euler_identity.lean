-- Prove2me | solution 1 for FamousTheorems.euler_identity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:07:09.038315+00:00
-- url     : https://prove2.me/submissions/7099b7ae-4116-4934-9b25-35673d4a0941

import Mathlib

theorem solution : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 :=
  Complex.exp_pi_mul_I
