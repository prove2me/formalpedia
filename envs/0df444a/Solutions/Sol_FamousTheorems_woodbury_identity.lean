-- Prove2me | solution 1 for FamousTheorems.woodbury_identity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:11:05.573991+00:00
-- url     : https://prove2.me/submissions/b07c6817-8512-4ab9-8370-0ad9095a2e06

import Mathlib

theorem solution {m n α : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [CommRing α] (A : Matrix n n α)
    (U : Matrix n m α) (C : Matrix m m α) (V : Matrix m n α) (hA : IsUnit A) (hC : IsUnit C)
    (hCVAU : IsUnit (C⁻¹ + V * A⁻¹ * U)) :
    (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ :=
  Matrix.add_mul_mul_inv_eq_sub A U C V hA hC hCVAU
