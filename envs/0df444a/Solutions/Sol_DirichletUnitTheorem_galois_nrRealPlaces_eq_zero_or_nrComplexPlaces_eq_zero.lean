-- Prove2me | solution 1 for DirichletUnitTheorem.galois_nrRealPlaces_eq_zero_or_nrComplexPlaces_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:19:34.423965+00:00
-- url     : https://prove2.me/submissions/4326c23a-6fbc-486d-a6b4-28684b69838d

import Mathlib
open NumberField

theorem solution (K : Type*) [Field K]
    [NumberField K] [IsGalois ℚ K] :
    InfinitePlace.nrRealPlaces K = 0 ∨ InfinitePlace.nrComplexPlaces K = 0 := by
  by_cases h : ∃ w : InfinitePlace K, w.IsReal
  · right
    obtain ⟨w, hw⟩ := h
    rw [NumberField.nrComplexPlaces_eq_zero_iff]
    refine ⟨fun w' => ?_⟩
    obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq (k := ℚ) (w := w) (w' := w')
      (Subsingleton.elim _ _)
    rw [← hσ]
    exact InfinitePlace.isReal_smul_iff.mpr hw
  · left
    push Not at h
    rw [NumberField.nrRealPlaces_eq_zero_iff]
    exact ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mp (h w)⟩
