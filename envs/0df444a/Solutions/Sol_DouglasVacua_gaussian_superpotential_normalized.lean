-- Prove2me | solution 1 for DouglasVacua.gaussian_superpotential_normalized
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:43:40.071669+00:00
-- url     : https://prove2.me/submissions/f9342c10-e5e6-422d-a513-0093ddf700c1

import Mathlib

open Real MeasureTheory

lemma dvGauss_plane (α : ℝ) (hα : 0 < α) :
    ∫ z : ℂ, Real.exp (-α * ‖z‖ ^ 2) = π / α := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hα, Complex.finrank_real_complex]
  norm_num

open Real MeasureTheory in
theorem solution (m : ℕ) (α : ℝ) (hα : 0 < α) :
    ∫ w : Fin m → ℂ, (α / π) ^ m * Real.exp (-α * ∑ I, ‖w I‖ ^ 2) = 1 := by
  have h2 : (fun w : Fin m → ℂ => (α / π) ^ m * Real.exp (-α * ∑ I, ‖w I‖ ^ 2)) =
      fun w => (α / π) ^ m * ∏ I, Real.exp (-α * ‖w I‖ ^ 2) := by
    funext w
    rw [Finset.mul_sum, Real.exp_sum]
  rw [h2, integral_const_mul,
    integral_fintype_prod_volume_eq_pow (fun z : ℂ => Real.exp (-α * ‖z‖ ^ 2)),
    dvGauss_plane α hα, Fintype.card_fin, ← mul_pow, div_mul_div_comm, mul_comm α π,
    div_self (by positivity), one_pow]

