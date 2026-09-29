-- Prove2me | solution 1 for FamousTheorems.add_pow
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:10:47.960954+00:00
-- url     : https://prove2.me/submissions/1cffebb2-6055-4b73-8935-b25c03201cc1

import Mathlib

theorem solution : ∀ {R : Type*} [CommSemiring R] (x y : R) (n : ℕ),
    (x + y) ^ n = ∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n - k) * (n.choose k) :=
  add_pow
