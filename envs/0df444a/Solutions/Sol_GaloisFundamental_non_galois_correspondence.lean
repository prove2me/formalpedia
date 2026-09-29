-- Prove2me | solution 1 for GaloisFundamental.non_galois_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T22:17:08.261442+00:00
-- url     : https://prove2.me/submissions/0391feab-9cd9-4888-a7ca-0dc6af6a51dd

import Mathlib

theorem solution (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (hE : ¬ IsGalois F E) :
    Function.Injective (fun H : Subgroup (E ≃ₐ[F] E) => IntermediateField.fixedField H) ∧
      ¬ Function.Surjective (fun H : Subgroup (E ≃ₐ[F] E) => IntermediateField.fixedField H) ∧
      Function.Surjective (fun K : IntermediateField F E => K.fixingSubgroup) ∧
      ¬ Function.Injective (fun K : IntermediateField F E => K.fixingSubgroup) ∧
      ∀ H : Subgroup (E ≃ₐ[F] E), IntermediateField.fixedField H ≠ ⊥ := by
  have hne : ∀ H : Subgroup (E ≃ₐ[F] E), IntermediateField.fixedField H ≠ ⊥ := by
    intro H hH
    apply hE
    apply IsGalois.of_fixedField_eq_bot
    apply le_antisymm _ bot_le
    rw [← hH, IntermediateField.le_iff_le, IntermediateField.fixingSubgroup_fixedField]
    exact le_top
  refine ⟨?_, ?_, ?_, ?_, hne⟩
  · intro H₁ H₂ h
    have := congrArg IntermediateField.fixingSubgroup h
    simpa only [IntermediateField.fixingSubgroup_fixedField] using this
  · rintro hs
    obtain ⟨H, hH⟩ := hs ⊥
    exact hne H hH
  · intro H
    exact ⟨IntermediateField.fixedField H, IntermediateField.fixingSubgroup_fixedField H⟩
  · intro hinj
    apply hne ⊤
    apply hinj
    simp only [IntermediateField.fixingSubgroup_fixedField, IntermediateField.fixingSubgroup_bot]
