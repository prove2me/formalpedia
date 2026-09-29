-- Prove2me | solution 1 for FamousTheorems.dirichlet_character_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:22:00.609972+00:00
-- url     : https://prove2.me/submissions/b58ca6ae-a97a-4ad1-bfc6-0e359dc64bce

import Mathlib

theorem solution (R : Type*) [CommRing R] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]
    [IsDomain R] {a : ZMod n} (ha : a ≠ 1) : ∑ χ : DirichletCharacter R n, χ a = 0 :=
  DirichletCharacter.sum_characters_eq_zero R ha
