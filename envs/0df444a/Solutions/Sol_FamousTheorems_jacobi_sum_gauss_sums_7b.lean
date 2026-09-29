-- Prove2me | solution 1 for FamousTheorems.jacobi_sum_gauss_sums_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:13:53.030308+00:00
-- url     : https://prove2.me/submissions/3a09cdfd-f475-42af-b90d-b7910151bc6f

import Mathlib

theorem solution {F F' : Type*} [Fintype F] [Field F] [Field F'] (hF : (Fintype.card F : F') ≠ 0)
    {χ φ : MulChar F F'} (hχφ : χ * φ ≠ 1) {ψ : AddChar F F'} (hψ : ψ.IsPrimitive) :
    jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ / gaussSum (χ * φ) ψ :=
  jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hF hχφ hψ
