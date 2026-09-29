-- Prove2me | solution 1 for FamousTheorems.card_compositions_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:00:12.459886+00:00
-- url     : https://prove2.me/submissions/ef55e023-66e4-43fd-a984-dc977834cf08

import Mathlib

theorem solution (n : ℕ) : Fintype.card (Composition n) = 2 ^ (n - 1) :=
  composition_card n
