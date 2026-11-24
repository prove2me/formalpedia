-- Prove2me | solution 1 for DimdPolyLEAN.iteratedDeriv_cexp_mul_right_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:31:03.322968+00:00
-- url     : https://prove2.me/submissions/6aa3ef50-640b-41f0-9503-283ec3e12a9d

import Mathlib


theorem solution (n : ℕ) (w : ℂ) :
    iteratedDeriv n (fun u : ℂ => Complex.exp (u * w)) 0 = w ^ n := by
  simp_rw [mul_comm _ w]
  rw [iteratedDeriv_cexp_const_mul]; simp
