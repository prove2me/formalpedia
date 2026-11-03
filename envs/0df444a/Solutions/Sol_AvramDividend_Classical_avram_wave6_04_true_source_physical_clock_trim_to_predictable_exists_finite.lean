-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_true_source_physical_clock_trim_to_predictable_exists_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:22:51.746353+00:00
-- url     : https://prove2.me/submissions/c26480f3-b401-40b9-b354-bb4dd5585ad4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      ∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A =
          ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
            Real.toNNReal).prod P) A := by
  classical
  have hσ : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      have hA0 : MeasurableSet A := (𝓕.rightCont.le ⊥) A hA
      exact (measurableSet_singleton (0 : ℝ≥0)).prod hA0
    · intro i A hA
      have hA0 : MeasurableSet A := (𝓕.rightCont.le i) A hA
      exact measurableSet_Ioi.prod hA0
  let μTime : Measure ℝ≥0 :=
    ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
  haveI hfiniteTime : IsFiniteMeasure
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))) := by
    infer_instance
  haveI : IsFiniteMeasure μTime :=
    Measure.isFiniteMeasure_map
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))) Real.toNNReal
  let μProd : Measure (ℝ≥0 × Ω) := μTime.prod P
  haveI : IsFiniteMeasure μProd := inferInstance
  refine ⟨μProd.trim hσ, ?_, ?_⟩
  · rw [trim_measurableSet_eq hσ MeasurableSet.univ]
    exact measure_lt_top _ _
  · intro A hA
    exact trim_measurableSet_eq hσ hA
