-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_marked_restricted_cell_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:53:34.982335+00:00
-- url     : https://prove2.me/submissions/6cad14f6-1b90-4139-94c7-3acb2408a884

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_finite_cell_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_cell_horizon_clip
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    M ((Ioc s (min t T) ×ˢ A) ×ˢ B) := by
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    @Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)
  let E : Set ((ℝ≥0 × Ω) × ℝ) := ((Ioc s t ×ˢ A) ×ˢ B)
  let S : Set ((ℝ≥0 × Ω) × ℝ) := {p | p.1.1 ≤ T}
  have hm : MeasurableSet E := by
    exact avram_p3_b_bvjump_original_predictable_finite_cell_measurable
      𝓕 s t A hA B hB
  change (M.restrict S) E = M ((Ioc s (min t T) ×ˢ A) ×ˢ B)
  calc
    (M.restrict S) E = M (E ∩ S) := Measure.restrict_apply hm
    _ = M ((Ioc s (min t T) ×ˢ A) ×ˢ B) := by
      exact congrArg M
        (avram_p3_b_bvjump_original_marked_cell_horizon_clip Ω s t T A B)
