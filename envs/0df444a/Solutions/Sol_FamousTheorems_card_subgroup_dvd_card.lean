-- Prove2me | solution 1 for FamousTheorems.card_subgroup_dvd_card
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:52:36.704249+00:00
-- url     : https://prove2.me/submissions/95a6d04f-b4a3-416b-8784-804298ce5a72

import Mathlib

theorem solution : ∀ {α : Type*} [Group α] (s : Subgroup α), Nat.card s ∣ Nat.card α :=
  Subgroup.card_subgroup_dvd_card
