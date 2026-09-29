-- Prove2me | solution 1 for FamousTheorems.intersecting_family_card_le_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:00:28.818655+00:00
-- url     : https://prove2.me/submissions/f0bcea57-709f-4b57-b8c9-d9d26b701cfd

import Mathlib

theorem solution {α : Type*} [BooleanAlgebra α] [Fintype α] {s : Finset α} (hs : (s : Set α).Intersecting) :
    2 * s.card ≤ Fintype.card α :=
  hs.card_le
