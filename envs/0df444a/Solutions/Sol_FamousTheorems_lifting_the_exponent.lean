-- Prove2me | solution 1 for FamousTheorems.lifting_the_exponent
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:25:50.525409+00:00
-- url     : https://prove2.me/submissions/7425ed44-5033-409f-b85c-5d97b589a3c0

import Mathlib

theorem solution {p : ℕ} (hp : p.Prime) (hp1 : Odd p) {x y : ℤ} (hxy : (p : ℤ) ∣ x - y) (hx : ¬(p : ℤ) ∣ x) (n : ℕ) :
    emultiplicity (p : ℤ) (x ^ n - y ^ n) = emultiplicity (p : ℤ) (x - y) + emultiplicity p n :=
  Int.emultiplicity_pow_sub_pow hp hp1 hxy hx n
