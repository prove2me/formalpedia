-- Prove2me | solution 1 for FamousTheorems.infinite_galois_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:53:58.873959+00:00
-- url     : https://prove2.me/submissions/2406285a-2f92-4fdf-9fd2-729e64a6fd27

import Mathlib

theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K] :
    (∀ L : IntermediateField k K, IntermediateField.fixedField L.fixingSubgroup = L) ∧
      ∀ H : ClosedSubgroup (K ≃ₐ[k] K),
        (IntermediateField.fixedField H.toSubgroup).fixingSubgroup = H.toSubgroup :=
  ⟨fun L => InfiniteGalois.fixedField_fixingSubgroup L, fun H => InfiniteGalois.fixingSubgroup_fixedField H⟩
