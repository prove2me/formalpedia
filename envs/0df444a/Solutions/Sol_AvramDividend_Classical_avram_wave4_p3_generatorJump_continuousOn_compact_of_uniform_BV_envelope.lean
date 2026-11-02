-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p3_generatorJump_continuousOn_compact_of_uniform_BV_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:56:11.187835+00:00
-- url     : https://prove2.me/submissions/024c43f6-e8f2-497a-b9da-712d769d790a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_min_one_abs_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (f : ℝ → ℝ) (hmono : Monotone f)
    (l u : ℝ)
    (hlinear : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y ∈ Iio (0 : ℝ),
        ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
          C * min 1 |y|)
    (hjump : ∀ x ∈ Icc l u,
      ∀ᵐ y ∂(X.ν.restrict (Iio 0)),
        ContinuousWithinAt
          (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand f z y)
          (Icc l u) x) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ y : ℝ, SpectrallyNegativeLevy.generatorIntegrand f x y
          ∂(X.ν.restrict (Iio 0)))
      (Icc l u) := by
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  obtain ⟨C, hC, hbound⟩ := hlinear
  have hdom : Integrable (fun y : ℝ => C * min 1 |y|) μ := by
    exact (boundedVariation_min_one_abs_integrable X hbv).const_mul C
  have hmeas (z : ℝ) :
      Measurable (fun y : ℝ =>
        SpectrallyNegativeLevy.generatorIntegrand f z y) := by
    have hf : Measurable f := hmono.measurable
    have hs : MeasurableSet (Ioo (-1 : ℝ) (1 : ℝ)) := measurableSet_Ioo
    unfold SpectrallyNegativeLevy.generatorIntegrand
    fun_prop (disch := assumption)
  have hnorm (z : ℝ) (hz : z ∈ Icc l u) :
      ∀ᵐ y ∂μ,
        ‖SpectrallyNegativeLevy.generatorIntegrand f z y‖ ≤
          C * min 1 |y| := by
    have hmem : ∀ᵐ y ∂μ, y ∈ Iio (0 : ℝ) := by
      change ∀ᵐ y ∂(X.ν.restrict (Iio (0 : ℝ))), y ∈ Iio (0 : ℝ)
      exact ae_restrict_mem measurableSet_Iio
    filter_upwards [hmem] with y hy
    exact hbound z hz y hy
  have hcont :
      Continuous (fun z : (Icc l u : Set ℝ) =>
        ∫ y : ℝ, SpectrallyNegativeLevy.generatorIntegrand f (z : ℝ) y ∂μ) := by
    apply (continuous_iff_seqContinuous).2
    intro v z hv
    have hv' : Tendsto (fun n => (v n : ℝ)) atTop (nhds (z : ℝ)) :=
      (continuous_subtype_val.tendsto z).comp hv
    have hvWithin : Tendsto (fun n => (v n : ℝ))
        atTop (nhdsWithin (z : ℝ) (Icc l u)) := by
      exact tendsto_nhdsWithin_iff.mpr
        ⟨hv', Filter.Eventually.of_forall (fun n => (v n).property)⟩
    have hpoint :
        ∀ᵐ y ∂μ,
          Tendsto (fun n =>
            SpectrallyNegativeLevy.generatorIntegrand f (v n : ℝ) y)
              atTop (nhds (SpectrallyNegativeLevy.generatorIntegrand f (z : ℝ) y)) := by
      filter_upwards [hjump (z : ℝ) z.property] with y hy
      exact hy.tendsto.comp hvWithin
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := fun y : ℝ => C * min 1 |y|)
      (fun n => (hmeas (v n : ℝ)).aestronglyMeasurable)
      hdom (fun n => hnorm (v n : ℝ) (v n).property) hpoint
  exact continuousOn_iff_continuous_restrict.mpr hcont
