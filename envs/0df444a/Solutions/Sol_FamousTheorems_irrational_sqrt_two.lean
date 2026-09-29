-- Prove2me | solution 1 for FamousTheorems.irrational_sqrt_two
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:52:36.487572+00:00
-- url     : https://prove2.me/submissions/ce9d5db1-69a4-403a-b7a2-ca4db21c46e9

import Mathlib

theorem solution : Irrational (Real.sqrt 2) :=
  irrational_sqrt_two
