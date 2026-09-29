-- Prove2me | solution 1 for FamousTheorems.marica_schonheim_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:23:18.267756+00:00
-- url     : https://prove2.me/submissions/8af25495-424d-40a2-b042-9758d5a9f5ad

import Mathlib

theorem solution {α : Type*} [DecidableEq α] [GeneralizedBooleanAlgebra α] (s : Finset α) : s.card ≤ (s.diffs s).card :=
  Finset.card_le_card_diffs s
