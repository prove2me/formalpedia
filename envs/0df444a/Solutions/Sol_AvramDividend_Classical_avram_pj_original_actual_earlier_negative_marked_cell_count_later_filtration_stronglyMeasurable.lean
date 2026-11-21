-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_actual_earlier_negative_marked_cell_count_later_filtration_stronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:26:14.336047+00:00
-- url     : https://prove2.me/submissions/1ac41155-3ce4-41f9-8052-2e6f4d9ef752

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a28_original_physical_Borel_cell_count_filtration_measurable_20261116
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The real original negative Lévy marked-jump count on an earlier
physical cell is strongly measurable in the true right-continuous
filtration at any subsequent grid time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (htu : t ≤ u)
    (B : Set ℝ) (hB : MeasurableSet B) :
    StronglyMeasurable[𝓕.rightCont u] (fun ω : Ω =>
      (((Measure.count.restrict {r : ℝ≥0 |
          0 < r ∧ X.X r ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) r ≠ 0}).map
        (fun r : ℝ≥0 => (r,
          X.X r ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) r)))
        (Ioc s t ×ˢ B)).toReal) := by
  have hm : Measurable[𝓕 t] (fun ω : Ω =>
      ((Measure.count.restrict {r : ℝ≥0 |
          0 < r ∧ X.X r ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) r ≠ 0}).map
        (fun r : ℝ≥0 => (r,
          X.X r ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) r)))
        (Ioc s t ×ˢ B)) :=
    avram_a28_original_physical_Borel_cell_count_filtration_measurable_20261116
      X s t B hB
  have hu : Measurable[𝓕.rightCont u] (fun ω : Ω =>
      ((Measure.count.restrict {r : ℝ≥0 |
          0 < r ∧ X.X r ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) r ≠ 0}).map
        (fun r : ℝ≥0 => (r,
          X.X r ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) r)))
        (Ioc s t ×ˢ B)) := by
    exact hm.mono ((𝓕.mono htu).trans (𝓕.le_rightCont u)) le_rfl
  exact (ENNReal.measurable_toReal.comp hu).stronglyMeasurable
