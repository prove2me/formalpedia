-- Prove2me | solution 1 for FamousTheorems.finite_field_iff_prime_power_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:14:16.387128+00:00
-- url     : https://prove2.me/submissions/96d8a27f-4201-4020-b64e-28c715c07c1c

import Mathlib

theorem solution {α : Type*} [Fintype α] : Nonempty (Field α) ↔ IsPrimePow (Fintype.card α) :=
  Fintype.nonempty_field_iff
