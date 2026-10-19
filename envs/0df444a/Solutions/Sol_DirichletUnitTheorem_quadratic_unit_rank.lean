-- Prove2me | solution 1 for DirichletUnitTheorem.quadratic_unit_rank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:20:02.899851+00:00
-- url     : https://prove2.me/submissions/59073da0-66b0-4849-b230-e1d565d71d03

import Mathlib
open NumberField

theorem solution (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    (Module.rank ℤ (Additive (𝓞 K)ˣ) = 1 ↔ IsTotallyReal K) ∧
      (Module.rank ℤ (Additive (𝓞 K)ˣ) = 0 ↔ IsTotallyComplex K) := by
  rw [← Module.finrank_eq_rank, Units.finrank_eq, Units.rank,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, ← NumberField.nrRealPlaces_eq_zero_iff,
    ← NumberField.nrComplexPlaces_eq_zero_iff, Nat.cast_eq_one, Nat.cast_eq_zero]
  rw [← InfinitePlace.card_add_two_mul_card_eq_rank] at hK
  omega
