-- Prove2me | solution 1 for FamousTheorems.sylow_count_dvd_index
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:58:58.587816+00:00
-- url     : https://prove2.me/submissions/f010f599-9ef9-43fe-867c-7684d250b11e

import Mathlib

theorem solution {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) ∣ (P : Subgroup G).index :=
  P.card_dvd_index
