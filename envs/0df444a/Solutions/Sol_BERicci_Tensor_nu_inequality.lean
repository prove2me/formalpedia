-- Prove2me | solution 1 for BERicci.Tensor.nu_inequality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:29:33.023621+00:00
-- url     : https://prove2.me/submissions/bbf9b291-0afa-4f3f-8ab3-920a114b4941

import Mathlib

set_option autoImplicit false

theorem solution (νX νY a b : ℝ) (hνX : 0 < νX) (hνY : 0 < νY)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    νX * νY / (νX + νY) * (a + b) ^ 2 ≤ νX * a ^ 2 + νY * b ^ 2 := by
  have hs : 0 < νX + νY := add_pos hνX hνY
  rw [div_mul_eq_mul_div, div_le_iff₀ hs]
  nlinarith [sq_nonneg (νX * a - νY * b)]
