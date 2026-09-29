-- Prove2me | solution 1 for FamousTheorems.poincare_rational_rotation_number_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:11:07.533035+00:00
-- url     : https://prove2.me/submissions/1c0a3634-7ffe-4191-9caa-6163b3241803

import Mathlib

theorem solution (f : CircleDeg1Lift) (hf : Continuous f) {m : ℤ} {n : ℕ} (hn : 0 < n) :
    f.translationNumber = m / n ↔ ∃ x, (f ^ n) x = x + m :=
  f.translationNumber_eq_rat_iff hf hn
