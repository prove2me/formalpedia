-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_rightcont_canonical_levy_intensity_initial_rectangle_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:49:19.58522+00:00
-- url     : https://prove2.me/submissions/cf0a8745-8fc6-49e5-86eb-3169e3555dd1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The canonical finite-horizon source Levy intensity charges no
original right-continuous predictable initial-time rectangle. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
        ∀ (B : Set ℝ), MeasurableSet B →
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
         μ.prod (X.ν.restrict (Iio (0 : ℝ))))
          (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) = 0) := by
  obtain ⟨μ, hfin, hagree, _hlintegral⟩ :=
    avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability X T
  letI : IsProbabilityMeasure P := X.isProbability
  letI : SigmaFinite X.ν :=
    avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields X
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) := inferInstance
  letI : IsFiniteMeasure μ := ⟨hfin⟩
  refine ⟨μ, hfin, hagree, ?_⟩
  have htime :
      (((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)
        ({(0 : ℝ≥0)}) = 0 := by
    rw [Measure.map_apply measurable_real_toNNReal
      (measurableSet_singleton (0 : ℝ≥0))]
    rw [Measure.restrict_apply
      (measurable_real_toNNReal (measurableSet_singleton (0 : ℝ≥0)))]
    have hsub :
        (Real.toNNReal ⁻¹' {(0 : ℝ≥0)}) ∩
          Icc 0 (T : ℝ) ⊆ {(0 : ℝ)} := by
      intro x hx
      have hx0 : (0 : ℝ) ≤ x := hx.2.1
      have hval : (x.toNNReal : ℝ) = x :=
        Real.coe_toNNReal x hx0
      have hz : x.toNNReal = (0 : ℝ≥0) := hx.1
      exact Set.mem_singleton_iff.mpr (by
        calc
          x = (x.toNNReal : ℝ) := hval.symm
          _ = 0 := congrArg (fun y : ℝ≥0 => (y : ℝ)) hz)
    exact le_antisymm
      ((measure_mono hsub).trans (by simp))
      bot_le
  intro A hA B hB
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hPred : MeasurableSet[𝓕.rightCont.predictable]
      ({(0 : ℝ≥0)} ×ˢ A) :=
    measurableSet_predictable_singleton_bot_prod hA
  have hμ0 : μ ({(0 : ℝ≥0)} ×ˢ A) = 0 := by
    rw [hagree _ hPred, Measure.prod_prod, htime, zero_mul]
  change (μ.prod (X.ν.restrict (Iio (0 : ℝ))))
    (({(0 : ℝ≥0)} ×ˢ A) ×ˢ B) = 0
  rw [Measure.prod_prod, hμ0, zero_mul]
