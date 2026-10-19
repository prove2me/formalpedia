-- Prove2me | solution 1 for DirichletUnitTheorem.unit_rank_eq_iff_totallyReal_totallyComplex_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:26:21.404083+00:00
-- url     : https://prove2.me/submissions/fc04a21d-a8dd-4223-9b9f-694a389a123f

import Mathlib
open NumberField

theorem solution (K L : Type*) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hKL : 1 < Module.finrank K L) :
    Module.finrank ℤ (Additive (𝓞 L)ˣ) = Module.finrank ℤ (Additive (𝓞 K)ˣ) ↔
      IsTotallyReal K ∧ IsTotallyComplex L ∧ Module.finrank K L = 2 := by
  have htow := Module.finrank_mul_finrank ℚ K L
  have hK := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hL := InfinitePlace.card_add_two_mul_card_eq_rank L
  have hcK := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  have hcL := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces L
  have hpK : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
  have hpL : 0 < Fintype.card (InfinitePlace L) := Fintype.card_pos
  rw [Units.finrank_eq, Units.finrank_eq, Units.rank, Units.rank,
    ← NumberField.nrComplexPlaces_eq_zero_iff, ← NumberField.nrRealPlaces_eq_zero_iff]
  obtain ⟨e, he⟩ : ∃ e, Module.finrank K L = e + 2 := ⟨Module.finrank K L - 2, by omega⟩
  rw [he] at htow ⊢
  have hnK : 0 < Module.finrank ℚ K := Module.finrank_pos
  rw [mul_add] at htow
  constructor
  · intro h
    have : Module.finrank ℚ K * e = 0 := by
      generalize Module.finrank ℚ K * e = m at *
      omega
    rcases Nat.mul_eq_zero.mp this with h0 | h0
    · omega
    · subst h0
      omega
  · rintro ⟨h1, h2, h3⟩
    have : e = 0 := by omega
    subst this
    simp only [mul_zero, zero_add] at htow
    omega
