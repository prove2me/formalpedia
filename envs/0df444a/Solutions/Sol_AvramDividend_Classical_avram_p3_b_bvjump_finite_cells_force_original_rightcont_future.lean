-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_finite_cells_force_original_rightcont_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:26:56.511443+00:00
-- url     : https://prove2.me/submissions/80e34bee-b00c-4370-8999-6e99624e191b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_cofinal_strict_future_sequence
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_rightcont_past_measurable_at_later_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_finite_cell_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_finite_rectangles_to_original_future
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_rightcont_future_of_decreasing_later_tails
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M N : @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _
       (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hRect : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        M ((Ioc s t ×ˢ A) ×ˢ B) =
        N ((Ioc s t ×ˢ A) ×ˢ B))
    (i : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont i] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    M ((Ioi i ×ˢ A) ×ˢ B) =
      N ((Ioi i ×ˢ A) ×ˢ B) := by
  obtain ⟨r, hr, hra, hcof⟩ :=
    avram_p3_b_bvjump_original_clock_cofinal_strict_future_sequence i
  have hAorig : ∀ n, MeasurableSet[𝓕 (r n)] A := by
    intro n
    exact avram_p3_b_bvjump_original_rightcont_past_measurable_at_later_time
      𝓕 i (r n) (hra n) A hA
  have hAr : ∀ n, MeasurableSet[𝓕.rightCont (r n)] A := by
    intro n
    exact (𝓕.le_rightCont (r n) A) (hAorig n)
  have hTail : ∀ n,
      M ((Ioi (r n) ×ˢ A) ×ˢ B) =
        N ((Ioi (r n) ×ˢ A) ×ˢ B) := by
    intro n
    apply avram_p3_b_bvjump_finite_rectangles_to_original_future
      𝓕 M N ?_ hRect (r n) A (hAorig n) B hB
    intro s t A' B' hA' hB'
    exact avram_p3_b_bvjump_original_predictable_finite_cell_measurable
      𝓕 s t A' hA' B' hB'
  exact avram_p3_b_bvjump_rightcont_future_of_decreasing_later_tails
    𝓕 M N i A B hB r hr hra hcof hAr hTail
