-- Prove2me | solution 1 for FamousTheorems.card_powerset
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:55:58.917478+00:00
-- url     : https://prove2.me/submissions/0804ba1f-31ac-4284-80a8-2dba64a71c6b

import Mathlib

theorem solution : ∀ {α : Type*} (s : Finset α), s.powerset.card = 2 ^ s.card :=
  Finset.card_powerset
