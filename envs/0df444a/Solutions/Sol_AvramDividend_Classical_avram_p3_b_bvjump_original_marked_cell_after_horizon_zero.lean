-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_marked_cell_after_horizon_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:20:32.091949+00:00
-- url     : https://prove2.me/submissions/40e4a55e-200e-4557-a582-95027ad2bc03

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_restricted_cell_measure
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
    (s t T : ℝ≥0) (hTs : T ≤ s)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) = 0 := by
  rw [avram_p3_b_bvjump_original_marked_restricted_cell_measure
    𝓕 M s t T A hA B hB]
  have hbound : min t T ≤ s := (min_le_right t T).trans hTs
  rw [Set.Ioc_eq_empty_of_le hbound]
  simp
