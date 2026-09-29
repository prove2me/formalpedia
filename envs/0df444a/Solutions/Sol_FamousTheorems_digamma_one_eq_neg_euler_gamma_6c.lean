-- Prove2me | solution 1 for FamousTheorems.digamma_one_eq_neg_euler_gamma_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:46:27.968285+00:00
-- url     : https://prove2.me/submissions/2ae1f3ec-6f9a-4b1f-a081-e1bd7be39901

import Mathlib

theorem solution : Complex.digamma 1 = -(Real.eulerMascheroniConstant : ℂ) :=
  Complex.digamma_one
