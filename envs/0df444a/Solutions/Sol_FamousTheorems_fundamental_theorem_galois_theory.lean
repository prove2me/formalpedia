-- Prove2me | solution 1 for FamousTheorems.fundamental_theorem_galois_theory
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:18:11.519872+00:00
-- url     : https://prove2.me/submissions/83b6ff49-d9aa-47b1-a045-92cb3c77b362

import Mathlib

theorem solution {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] :
    (∀ K : IntermediateField F E, IntermediateField.fixedField K.fixingSubgroup = K) ∧
      ∀ H : Subgroup (E ≃ₐ[F] E), (IntermediateField.fixedField H).fixingSubgroup = H :=
  ⟨fun K => IsGalois.fixedField_fixingSubgroup K, fun H => IntermediateField.fixingSubgroup_fixedField H⟩
