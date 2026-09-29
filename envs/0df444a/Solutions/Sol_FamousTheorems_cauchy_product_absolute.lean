-- Prove2me | solution 1 for FamousTheorems.cauchy_product_absolute
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:31:12.914981+00:00
-- url     : https://prove2.me/submissions/77c8ae22-6aac-4d0b-9850-202cad21b318

import Mathlib

theorem solution {R : Type*} [NormedRing R] [CompleteSpace R] {f g : ℕ → R} (hf : Summable fun n => ‖f n‖)
    (hg : Summable fun n => ‖g n‖) :
    (∑' n, f n) * (∑' n, g n) = ∑' n, ∑ k ∈ Finset.range (n + 1), f k * g (n - k) :=
  tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg
