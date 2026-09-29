-- Prove2me | solution 1 for FamousTheorems.second_supplementary_law_qr
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:12:07.827323+00:00
-- url     : https://prove2.me/submissions/2c332a9b-c1ad-4419-8bde-2c20760b5282

import Mathlib

theorem solution {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
  ZMod.exists_sq_eq_two_iff hp
