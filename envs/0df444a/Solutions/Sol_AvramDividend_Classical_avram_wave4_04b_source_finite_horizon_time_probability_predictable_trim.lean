-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_source_finite_horizon_time_probability_predictable_trim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:30:15.112817+00:00
-- url     : https://prove2.me/submissions/2ce39b3e-5565-4896-9d8a-141c5ba2e663

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      ∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hcompact : IsCompact (Icc (0 : ℝ) (T : ℝ)) := isCompact_Icc
  have hT : (volume : Measure ℝ) (Icc 0 (T : ℝ)) < ⊤ :=
    hcompact.measure_lt_top
  let ηReal : Measure ℝ := (volume : Measure ℝ).restrict (Icc 0 (T : ℝ))
  have hηReal : ηReal Set.univ < ⊤ := by simpa [ηReal] using hT
  letI : IsFiniteMeasure ηReal := ⟨hηReal⟩
  let η : Measure ℝ≥0 := ηReal.map Real.toNNReal
  letI : IsFiniteMeasure η := Measure.isFiniteMeasure_map ηReal Real.toNNReal
  let ξ : Measure (ℝ≥0 × Ω) := η.prod P
  letI : IsFiniteMeasure ξ := by dsimp [ξ]; infer_instance
  have hpred : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply MeasureTheory.measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact (measurableSet_singleton (⊥ : ℝ≥0)).prod ((𝓕.rightCont.le ⊥) A hA)
    · intro i A hA
      exact (measurableSet_Ioi).prod ((𝓕.rightCont.le i) A hA)
  let μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable) := ξ.trim hpred
  have hμ : μ Set.univ < ⊤ := by
    letI : IsFiniteMeasure μ := isFiniteMeasure_trim hpred
    exact measure_lt_top _ _
  refine ⟨μ, hμ, ?_⟩
  intro A hA
  change ξ.trim hpred A = ξ A
  exact trim_measurableSet_eq hpred hA
