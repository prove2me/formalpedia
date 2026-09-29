-- Prove2me | solution 1 for FamousTheorems.euler_homogeneous_function_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:57:39.759995+00:00
-- url     : https://prove2.me/submissions/f23201cf-fb00-40a9-8724-7abf934c76c3

import Mathlib

theorem solution {R σ : Type*} [CommSemiring R] [Fintype σ] {φ : MvPolynomial σ R} {n : ℕ} (hφ : φ.IsHomogeneous n) :
    ∑ i : σ, MvPolynomial.X i * MvPolynomial.pderiv i φ = n • φ :=
  hφ.sum_X_mul_pderiv
