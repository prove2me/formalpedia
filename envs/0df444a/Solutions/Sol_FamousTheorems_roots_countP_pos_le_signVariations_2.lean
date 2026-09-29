-- Prove2me | solution 2 for FamousTheorems.roots_countP_pos_le_signVariations
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T22:41:42.290666+00:00
-- url     : https://prove2.me/submissions/28133b06-599b-4156-9bd7-de62de7436f5

import Mathlib.Algebra.Polynomial.RuleOfSigns

theorem solution : ∀ {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (p : Polynomial R),
    (p.roots.countP fun x => 0 < x) ≤ p.signVariations := by
  intro R _ _ _ p
  exact Polynomial.roots_countP_pos_le_signVariations p
