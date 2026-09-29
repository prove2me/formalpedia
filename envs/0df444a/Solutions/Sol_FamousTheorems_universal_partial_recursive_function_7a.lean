-- Prove2me | solution 1 for FamousTheorems.universal_partial_recursive_function_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:53:14.547332+00:00
-- url     : https://prove2.me/submissions/5ff182e2-229a-4bac-86e3-23e5065896a8

import Mathlib

theorem solution : Partrec₂ Nat.Partrec.Code.eval :=
  Nat.Partrec.Code.eval_part
