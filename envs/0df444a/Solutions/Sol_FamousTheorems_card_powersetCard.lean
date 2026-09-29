-- Prove2me | solution 1 for FamousTheorems.card_powersetCard
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:55:58.872782+00:00
-- url     : https://prove2.me/submissions/48aa8215-699d-4374-b90f-e2b22a4030c0

import Mathlib

theorem solution : ∀ {α : Type*} (n : ℕ) (s : Finset α), (Finset.powersetCard n s).card = s.card.choose n :=
  Finset.card_powersetCard
