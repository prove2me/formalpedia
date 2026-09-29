-- Prove2me | solution 1 for FamousTheorems.gaussian_integral
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:14:27.322777+00:00
-- url     : https://prove2.me/submissions/318a2201-7aac-4ac0-a617-a5b8fdafc3ff

import Mathlib

theorem solution (b : ℝ) : ∫ x : ℝ, Real.exp (-b * x ^ 2) = Real.sqrt (Real.pi / b) :=
  integral_gaussian b
