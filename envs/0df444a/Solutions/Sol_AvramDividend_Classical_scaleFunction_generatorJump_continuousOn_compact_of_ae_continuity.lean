-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorJump_continuousOn_compact_of_ae_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:15:53.816992+00:00
-- url     : https://prove2.me/submissions/dd5a1d95-4822-4ee5-b12e-cc739c7b931f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_uniform_generatorIntegrand_bound_on_compact
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_continuousWithinAt_integral_of_integrable_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hjump : ∀ x ∈ Icc l u,
      ∀ᵐ y ∂(X.ν.restrict (Iio 0)),
        ContinuousWithinAt
          (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand W z y)
          (Icc l u) x) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ y : ℝ, SpectrallyNegativeLevy.generatorIntegrand W x y
          ∂(X.ν.restrict (Iio 0)))
      (Icc l u) := by
  let μ : Measure ℝ := X.ν.restrict (Iio 0)
  obtain ⟨C, hC, hCb⟩ :=
    scaleFunction_uniform_generatorIntegrand_bound_on_compact
      X q W hW a l u hl hlu hu hC2
  have hmin_meas :
      AEStronglyMeasurable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by
    fun_prop
  have hmin_nonneg :
      0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) := by
    filter_upwards with y
    positivity
  have hmin_full :
      Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hmin_meas hmin_nonneg).mp (ne_of_lt X.ν_integrable)
  have hmin : Integrable (fun y : ℝ => min 1 (y ^ 2)) μ :=
    hmin_full.mono_measure Measure.restrict_le_self
  have hbound_int :
      Integrable (fun y : ℝ => C * min 1 (y ^ 2)) μ :=
    hmin.const_mul C
  have hmeas : ∀ x ∈ Icc l u,
      AEStronglyMeasurable
        (SpectrallyNegativeLevy.generatorIntegrand W x) μ := by
    intro x hx
    exact scaleFunction_generatorIntegrand_aestronglyMeasurable
      X q W hW x
  have hbound : ∀ x ∈ Icc l u,
      ∀ᵐ y ∂μ, ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
        C * min 1 (y ^ 2) := by
    intro x hx
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := X.ν) measurableSet_Iio] with y hy
    exact hCb x hx y hy
  intro x hx
  exact continuousWithinAt_integral_of_integrable_uniform_bound
    μ (Icc l u)
    (fun z y => SpectrallyNegativeLevy.generatorIntegrand W z y)
    (fun y => C * min 1 (y ^ 2)) x hx
    hmeas hbound hbound_int (hjump x hx)
