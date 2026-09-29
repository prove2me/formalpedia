-- Prove2me | solution 1 for FamousTheorems.cauchy_theorem_finite_groups
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:10:17.783809+00:00
-- url     : https://prove2.me/submissions/a3b8a3a6-3820-476e-a63f-f08ae5c33698

import Mathlib

theorem solution {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (hdvd : p ∣ Nat.card G) :
    ∃ x : G, orderOf x = p :=
  exists_prime_orderOf_dvd_card' p hdvd
