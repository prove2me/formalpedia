-- Prove2me | solution 1 for FamousTheorems.group_order_prime_sq_abelian
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:03:41.222071+00:00
-- url     : https://prove2.me/submissions/c71b73ba-a6c7-4ca7-926f-7dc354b21ed4

import Mathlib

theorem solution {p : ℕ} {G : Type*} [Group G] [Fact p.Prime] (h : Nat.card G = p ^ 2) : IsMulCommutative G :=
  IsPGroup.isMulCommutative_of_card_eq_prime_sq h
