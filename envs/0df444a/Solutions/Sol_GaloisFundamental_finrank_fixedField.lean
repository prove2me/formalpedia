-- Prove2me | solution 1 for GaloisFundamental.finrank_fixedField
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T22:17:04.370016+00:00
-- url     : https://prove2.me/submissions/07357c82-1657-4bb3-bf65-d2c22872ca85

import Mathlib

theorem solution (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (H : Subgroup (E ≃ₐ[F] E)) :
    Module.finrank (IntermediateField.fixedField H) E = Nat.card H ∧
      Module.finrank F (IntermediateField.fixedField H) = H.index := by
  have h1 : Module.finrank (IntermediateField.fixedField H) E = Nat.card H :=
    IntermediateField.finrank_fixedField_eq_card H
  refine ⟨h1, ?_⟩
  have h2 : Nat.card (E ≃ₐ[F] E) = Module.finrank F E := IsGalois.card_aut_eq_finrank F E
  have h3 := Module.finrank_mul_finrank F (IntermediateField.fixedField H) E
  have h4 := H.card_mul_index
  have hpos : 0 < Nat.card H := Nat.card_pos
  rw [h1] at h3
  have : Module.finrank F (IntermediateField.fixedField H) * Nat.card H = H.index * Nat.card H := by
    rw [h3, ← h2, ← h4, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hpos this
