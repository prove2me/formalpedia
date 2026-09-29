-- Prove2me | solution 1 for FamousTheorems.card_odds_eq_card_distincts
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:55:58.946807+00:00
-- url     : https://prove2.me/submissions/feac73b7-a29a-4a34-b0d1-fe1de478167f

import Mathlib

theorem solution : ∀ n : ℕ, (Nat.Partition.odds n).card = (Nat.Partition.distincts n).card :=
  Nat.Partition.card_odds_eq_card_distincts
