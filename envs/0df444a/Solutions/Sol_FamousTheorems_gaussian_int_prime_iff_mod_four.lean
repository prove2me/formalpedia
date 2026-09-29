-- Prove2me | solution 1 for FamousTheorems.gaussian_int_prime_iff_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:16:51.276885+00:00
-- url     : https://prove2.me/submissions/7aab19ad-a4b6-49fb-b5e3-37e0bbd8b4b9

import Mathlib

theorem solution (p : ℕ) [Fact p.Prime] : Prime (p : GaussianInt) ↔ p % 4 = 3 :=
  GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p
