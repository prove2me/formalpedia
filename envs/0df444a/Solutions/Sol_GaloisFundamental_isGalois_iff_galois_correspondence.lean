-- Prove2me | solution 1 for GaloisFundamental.isGalois_iff_galois_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T19:04:29.869155+00:00
-- url     : https://prove2.me/submissions/fad0eae6-40b5-4b99-8e38-d874b0ee4c20

import Mathlib

namespace GaloisFundamental

theorem isGalois_iff_galois_correspondence_aux (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    IsGalois F E ↔
      ((∀ K : IntermediateField F E, IntermediateField.fixedField K.fixingSubgroup = K) ∧
        ∀ H : Subgroup (E ≃ₐ[F] E), (IntermediateField.fixedField H).fixingSubgroup = H) := by
  constructor
  · intro h
    exact ⟨fun K => IsGalois.fixedField_fixingSubgroup K,
      fun H => IntermediateField.fixingSubgroup_fixedField H⟩
  · rintro ⟨h1, -⟩
    refine IsGalois.of_fixedField_eq_bot F E ?_
    have hbot : IntermediateField.fixedField (IntermediateField.fixingSubgroup
        (⊥ : IntermediateField F E)) = ⊥ := h1 ⊥
    rwa [IntermediateField.fixingSubgroup_bot] at hbot

end GaloisFundamental

open GaloisFundamental

theorem solution (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    IsGalois F E ↔
      ((∀ K : IntermediateField F E, IntermediateField.fixedField K.fixingSubgroup = K) ∧
        ∀ H : Subgroup (E ≃ₐ[F] E), (IntermediateField.fixedField H).fixingSubgroup = H) :=
  isGalois_iff_galois_correspondence_aux F E
