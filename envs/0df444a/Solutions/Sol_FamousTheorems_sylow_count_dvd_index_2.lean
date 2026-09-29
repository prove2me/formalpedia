-- Prove2me | solution 2 for FamousTheorems.sylow_count_dvd_index
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T22:00:30.424196+00:00
-- url     : https://prove2.me/submissions/a5f0783f-81a8-407a-bba7-5f1d708d8e76

import Mathlib

theorem solution {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) ∣ (P : Subgroup G).index :=
  P.card_dvd_index
