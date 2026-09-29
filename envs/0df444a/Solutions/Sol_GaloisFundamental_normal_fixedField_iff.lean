-- Prove2me | solution 1 for GaloisFundamental.normal_fixedField_iff
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T22:16:56.718089+00:00
-- url     : https://prove2.me/submissions/7231759b-f6cb-404e-b4f7-09299af2744e

import Mathlib

theorem solution (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (H : Subgroup (E ≃ₐ[F] E)) :
    Normal F (IntermediateField.fixedField H) ↔ H.Normal := by
  constructor
  · intro hN
    haveI : Algebra.IsSeparable F (IntermediateField.fixedField H) :=
      Algebra.isSeparable_tower_bot_of_isSeparable F (IntermediateField.fixedField H) E
    haveI : IsGalois F (IntermediateField.fixedField H) := ⟨⟩
    have h := IsGalois.fixingSubgroup_normal_of_isGalois (K := F) (L := E)
      (IntermediateField.fixedField H)
    rwa [IntermediateField.fixingSubgroup_fixedField] at h
  · intro hH
    exact (IsGalois.of_fixedField_normal_subgroup H).to_normal
