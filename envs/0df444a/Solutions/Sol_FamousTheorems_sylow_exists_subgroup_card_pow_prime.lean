-- Prove2me | solution 1 for FamousTheorems.sylow_exists_subgroup_card_pow_prime
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:10:47.965542+00:00
-- url     : https://prove2.me/submissions/bad811fa-74ad-4af7-a0ce-b0a4b5ca1240

import Mathlib

theorem solution : ∀ {G : Type*} [Group G] [Finite G] (p : ℕ) {n : ℕ} [Fact (Nat.Prime p)],
    p ^ n ∣ Nat.card G → ∃ K : Subgroup G, Nat.card K = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime
