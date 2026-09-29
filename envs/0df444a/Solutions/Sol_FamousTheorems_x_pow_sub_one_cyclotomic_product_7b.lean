-- Prove2me | solution 1 for FamousTheorems.x_pow_sub_one_cyclotomic_product_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:05:40.636773+00:00
-- url     : https://prove2.me/submissions/bfd24494-6985-45b3-9c7a-94f6212854be

import Mathlib

theorem solution {n : ℕ} (hn : 0 < n) (R : Type*) [CommRing R] :
    ∏ d ∈ n.divisors, Polynomial.cyclotomic d R = Polynomial.X ^ n - 1 :=
  Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn R
