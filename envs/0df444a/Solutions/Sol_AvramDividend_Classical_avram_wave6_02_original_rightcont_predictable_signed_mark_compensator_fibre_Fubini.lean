-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:47:47.677484+00:00
-- url     : https://prove2.me/submissions/e3d875f4-3ac9-47ca-87c5-8a82766871a1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (∀ G : ((ℝ≥0 × Ω) × ℝ) → ℝ,
        Measurable[(@Prod.instMeasurableSpace _ _
          (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))] G →
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
          Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) →
        Integrable
          (fun ω => ∫ t, ∫ z, G ((t, ω), z)
            ∂(X.ν.restrict (Iio (0 : ℝ)))
            ∂(((volume : Measure ℝ).restrict
              (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
        (∫ ω, (∫ t, ∫ z, G ((t, ω), z)
          ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) =
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
          ∫ p, G p ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))))  := by
  classical
  obtain ⟨μ, hμ, hμclock, _⟩ :=
    avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability X T
  refine ⟨μ, hμ, hμclock, ?_⟩
  intro G hGm hGint
  letI : IsProbabilityMeasure P := X.isProbability
  let νneg : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  letI : SFinite νneg := levy_negative_jump_measure_sFinite X
  let ηReal : Measure ℝ := (volume : Measure ℝ).restrict (Icc 0 (T : ℝ))
  have hηReal : ηReal Set.univ < ⊤ := by
    simpa [ηReal] using (isCompact_Icc.measure_lt_top :
      (volume : Measure ℝ) (Icc 0 (T : ℝ)) < ⊤)
  letI : IsFiniteMeasure ηReal := ⟨hηReal⟩
  let η : Measure ℝ≥0 := ηReal.map Real.toNNReal
  letI : IsFiniteMeasure η := Measure.isFiniteMeasure_map ηReal Real.toNNReal
  let ξ : Measure (ℝ≥0 × Ω) := η.prod P
  have hpred : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply MeasureTheory.measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact (measurableSet_singleton (⊥ : ℝ≥0)).prod
        ((𝓕.rightCont.le ⊥) A hA)
    · intro i A hA
      exact measurableSet_Ioi.prod ((𝓕.rightCont.le i) A hA)
  have hμeq : μ = ξ.trim hpred := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    apply Measure.ext
    intro A hA
    calc
      μ A = ξ A := by simpa only [ξ, η, ηReal] using hμclock A hA
      _ = ξ.trim hpred A := (trim_measurableSet_eq hpred hA).symm
  let f : (ℝ≥0 × Ω) → ℝ := fun p => ∫ z, G (p, z) ∂νneg
  have hfStrong : StronglyMeasurable[𝓕.rightCont.predictable] f := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    exact StronglyMeasurable.integral_prod_right hGm.stronglyMeasurable
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  letI : SFinite μ := inferInstance
  have hfIntμ : Integrable f μ := hGint.integral_prod_left
  have hfIntξ : Integrable f ξ := by
    rw [hμeq] at hfIntμ
    exact integrable_of_integrable_trim hpred hfIntμ
  have htrim : (∫ p, f p ∂μ) = (∫ p, f p ∂ξ) := by
    rw [hμeq]
    exact (integral_trim hpred hfStrong).symm
  have hprod : (∫ p, G p ∂(μ.prod νneg)) = (∫ p, f p ∂μ) :=
    MeasureTheory.integral_prod G hGint
  change Integrable (fun ω => ∫ t, ∫ z, G ((t, ω), z) ∂νneg ∂η) P ∧
    (∫ ω, (∫ t, ∫ z, G ((t, ω), z) ∂νneg ∂η) ∂P) =
      (∫ p, G p ∂(μ.prod νneg))
  refine ⟨?_, ?_⟩
  · exact hfIntξ.integral_prod_right
  · calc
      (∫ ω, (∫ t, ∫ z, G ((t, ω), z) ∂νneg ∂η) ∂P) =
          (∫ p, f p ∂ξ) :=
        (MeasureTheory.integral_prod_symm f hfIntξ).symm
      _ = ∫ p, f p ∂μ := htrim.symm
      _ = ∫ p, G p ∂(μ.prod νneg) := hprod.symm