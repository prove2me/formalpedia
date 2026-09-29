-- Prove2me | solution 1 for GaloisFundamental.le_iff_fixedField_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T18:39:43.515566+00:00
-- url     : https://prove2.me/submissions/bad80f6e-1185-46ef-884e-8add2c77e440

import Mathlib

namespace GaloisFundamental

theorem le_iff_fixedField (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (H₁ H₂ : Subgroup (E ≃ₐ[F] E)) :
    H₁ ≤ H₂ ↔ IntermediateField.fixedField H₂ ≤ IntermediateField.fixedField H₁ := by
  constructor
  · intro h
    exact IntermediateField.fixedField_le h
  · intro h
    have hle : H₁ ≤ IntermediateField.fixingSubgroup (IntermediateField.fixedField H₂) :=
      (IntermediateField.le_iff_le (K := IntermediateField.fixedField H₂) (H := H₁)).mp h
    rw [IntermediateField.fixingSubgroup_fixedField H₂] at hle
    exact hle

end GaloisFundamental

open GaloisFundamental

theorem solution (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (H₁ H₂ : Subgroup (E ≃ₐ[F] E)) :
    H₁ ≤ H₂ ↔ IntermediateField.fixedField H₂ ≤ IntermediateField.fixedField H₁ :=
  le_iff_fixedField F E H₁ H₂
