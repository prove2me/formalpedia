-- Prove2me | solution 1 for FamousTheorems.euler_criterion_zmod
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:11:06.507348+00:00
-- url     : https://prove2.me/submissions/2ce4da47-f01e-49c3-83f8-43ca1c40cc05

import Mathlib

theorem solution (p : ℕ) [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) : IsSquare a ↔ a ^ (p / 2) = 1 :=
  ZMod.euler_criterion p ha
