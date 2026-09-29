-- Prove2me | solution 1 for FamousTheorems.integral_inv_one_add_sq_eq_pi_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:30:38.135748+00:00
-- url     : https://prove2.me/submissions/8fa99ce9-16ff-4bfa-ae08-6bcdaae38346

import Mathlib

open MeasureTheory

theorem solution : ∫ x : ℝ, (1 + x ^ 2)⁻¹ = Real.pi :=
  integral_univ_inv_one_add_sq
