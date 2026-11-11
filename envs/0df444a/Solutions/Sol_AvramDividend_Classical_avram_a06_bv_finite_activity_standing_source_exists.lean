-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_bv_finite_activity_standing_source_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:17:18.710704+00:00
-- url     : https://prove2.me/submissions/6091682b-ccb6-4456-af07-f5a9e03f414c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_concrete_diffuse_compound_source

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The finite-activity standing source follows once the original filtered
compound-Poisson process has been constructed with its exact parameters. -/
theorem solution :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
        X.Standing ∧ X.BoundedVariation ∧
        X.ν (Iio (0 : ℝ)) < ⊤ := by
  obtain ⟨P, 𝓕, X, hBV, hFinite, hPos, hNonzero, hInt, hAc⟩ :=
    avram_a06_bv_concrete_diffuse_compound_source
  refine ⟨P, 𝓕, X, ?_, hBV, hFinite⟩
  refine ⟨?_, hInt, ?_⟩
  · intro hMono
    rcases hMono.2 with hLe | hZero
    · exact (not_le_of_gt hPos) hLe
    · exact hNonzero hZero
  · right
    right
    exact hAc
