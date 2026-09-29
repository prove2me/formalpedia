-- Prove2me | solution 1 for FamousTheorems.roots_countP_pos_le_signVariations
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:36:47.29904+00:00
-- url     : https://prove2.me/submissions/77c909e9-a49b-43d4-a074-ff582e71a361

import Mathlib

theorem solution : ∀ {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (p : Polynomial R),
    (p.roots.countP fun x => 0 < x) ≤ p.signVariations :=
  fun p => Polynomial.roots_countP_pos_le_signVariations p
