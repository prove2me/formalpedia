-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_original_predictable_time_section_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:36:47.035456+00:00
-- url     : https://prove2.me/submissions/a6bb5c19-da77-414a-8b55-d8d8330239fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original right-continuous predictable sources have measurable time traces. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ)
    (hH : Measurable[𝓕.rightCont.predictable] H) :
    ∀ ω, Measurable (fun t : ℝ≥0 => H (t, ω)) := by
  have hPredLe : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      change MeasurableSet[𝓕.rightCont ⊥] A at hA
      have hA' : MeasurableSet[mΩ] A :=
        (MeasurableSpace.le_def.mp (𝓕.rightCont.le ⊥)) A hA
      exact (show MeasurableSet ({⊥} : Set ℝ≥0) from
        measurableSet_singleton (⊥ : ℝ≥0)).prod hA'
    · intro t A hA
      change MeasurableSet[𝓕.rightCont t] A at hA
      exact measurableSet_Ioi.prod
        ((MeasurableSpace.le_def.mp (𝓕.rightCont.le t)) A hA)
  have hProd : Measurable H := hH.mono hPredLe le_rfl
  intro ω
  exact hProd.comp (measurable_id.prodMk measurable_const)
