-- Prove2me | solution 1 for FamousTheorems.jacobi_sum_mul_inv_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:14:35.950907+00:00
-- url     : https://prove2.me/submissions/c7d5dfe8-73b3-4557-847e-a6e8309bd644

import Mathlib

theorem solution {F F' : Type*} [Fintype F] [Field F] [Field F'] (hchar : ringChar F' ≠ ringChar F)
    {χ φ : MulChar F F'} (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) :
    jacobiSum χ φ * jacobiSum χ⁻¹ φ⁻¹ = Fintype.card F :=
  jacobiSum_mul_jacobiSum_inv hchar hχ hφ hχφ
