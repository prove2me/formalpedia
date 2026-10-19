-- Prove2me | solution 1 for ExploreFirst.LargeT.product_ge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:33:38.20418+00:00
-- url     : https://prove2.me/submissions/5f226550-ecb6-46ce-b2cc-90b37449208f

import Mathlib

set_option autoImplicit false

theorem solution (a b c : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    1 - (a + b + c) ≤ (1 - a) * (1 - b) * (1 - c) := by
  nlinarith [mul_nonneg (mul_nonneg ha0 hb0) (sub_nonneg.2 hc1), mul_nonneg ha0 hc0,
    mul_nonneg hb0 hc0]
