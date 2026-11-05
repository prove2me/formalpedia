-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_marked_restricted_source_horizon_clip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:26:01.398212+00:00
-- url     : https://prove2.me/submissions/718b65f8-89b7-4d6c-ade6-1a7ff50d8f00

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_restricted_cell_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The restriction to the stopped horizon clips the source's marked cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (s t T : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) =
      (M.restrict {p | p.1.1 ≤ T})
        ((Ioc s (min t T) ×ˢ A) ×ˢ B) := by
  calc
    (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) =
        M ((Ioc s (min t T) ×ˢ A) ×ˢ B) :=
      avram_p3_b_bvjump_original_marked_restricted_cell_measure 𝓕 M s t T A hA B hB
    _ = (M.restrict {p | p.1.1 ≤ T})
          ((Ioc s (min t T) ×ˢ A) ×ˢ B) := by
      have h := avram_p3_b_bvjump_original_marked_restricted_cell_measure
        𝓕 M s (min t T) T A hA B hB
      simpa only [min_assoc, min_self] using h.symm
