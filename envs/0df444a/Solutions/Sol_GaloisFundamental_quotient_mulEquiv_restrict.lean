-- Prove2me | solution 1 for GaloisFundamental.quotient_mulEquiv_restrict
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T22:16:49.07288+00:00
-- url     : https://prove2.me/submissions/2bce701d-a289-4383-8ad8-96915e482773

import Mathlib

theorem solution (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (H : Subgroup (E ≃ₐ[F] E)) [H.Normal]
    [Normal F (IntermediateField.fixedField H)] :
    ∃ φ : ((E ≃ₐ[F] E) ⧸ H) ≃*
        (IntermediateField.fixedField H ≃ₐ[F] IntermediateField.fixedField H),
      ∀ σ : E ≃ₐ[F] E,
        φ (QuotientGroup.mk σ) = AlgEquiv.restrictNormalHom (IntermediateField.fixedField H) σ :=
  ⟨IsGalois.normalAutEquivQuotient H, fun σ => IsGalois.normalAutEquivQuotient_apply H σ⟩
