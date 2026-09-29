-- Prove2me | solution 1 for FamousTheorems.add_one_le_exp_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:30:12.847795+00:00
-- url     : https://prove2.me/submissions/5453b22c-1068-4669-900a-91840bcf9fb0

import Mathlib

theorem solution (x : ℝ) : x + 1 ≤ Real.exp x :=
  Real.add_one_le_exp x
