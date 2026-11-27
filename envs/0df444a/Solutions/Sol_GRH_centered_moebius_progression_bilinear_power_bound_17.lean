-- Prove2me | solution 17 for GRH.centered_moebius_progression_bilinear_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T01:49:21.67354+00:00
-- url     : https://prove2.me/submissions/413f71d4-395a-4e35-87f9-cfe99ce96800
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_centered_moebius_of_one_split_prime_class_at_factorial_squares
import Theorems.Thm_GRH_cofinal_lower_bound_for_completely_split_primes_at_squares

theorem solution
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ C * ((N : ℝ) + 1) ^ σ :=
  (GRH.centered_moebius_of_one_split_prime_class_at_factorial_squares.1
    GRH.cofinal_lower_bound_for_completely_split_primes_at_squares) q a ha σ hhalf hone
