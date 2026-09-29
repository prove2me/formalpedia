-- Prove2me | solution 1 for FamousTheorems.euler_integral_log_sin_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:46:12.091952+00:00
-- url     : https://prove2.me/submissions/843a13a6-24cd-425b-a3a1-58b4a6217c8a

import Mathlib

theorem solution :
    ∫ x in (0 : ℝ)..Real.pi, Real.log (Real.sin x) = -Real.log 2 * Real.pi :=
  integral_log_sin_zero_pi
