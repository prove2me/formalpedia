-- Prove2me | solution 1 for FamousTheorems.card_derangements_eq_numDerangements
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:17:24.731921+00:00
-- url     : https://prove2.me/submissions/3c2b518b-90da-4ca7-8747-b1dfbfeffdc6

import Mathlib

theorem solution : ∀ (α : Type*) [Fintype α] [DecidableEq α],
    Fintype.card (derangements α) = numDerangements (Fintype.card α) :=
  card_derangements_eq_numDerangements
