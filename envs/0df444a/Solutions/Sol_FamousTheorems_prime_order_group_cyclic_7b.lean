-- Prove2me | solution 1 for FamousTheorems.prime_order_group_cyclic_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:48:54.281385+00:00
-- url     : https://prove2.me/submissions/71a58555-fbde-4917-9358-4cc5d68e0c4f

import Mathlib

theorem solution {G : Type*} [Group G] {p : ℕ} [Fact (Nat.Prime p)] (h : Nat.card G = p) : IsCyclic G :=
  isCyclic_of_prime_card h
