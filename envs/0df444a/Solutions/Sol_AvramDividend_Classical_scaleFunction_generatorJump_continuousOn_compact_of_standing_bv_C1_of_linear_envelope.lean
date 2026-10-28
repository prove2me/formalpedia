-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorJump_continuousOn_compact_of_standing_bv_C1_of_linear_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:50:14.48649+00:00
-- url     : https://prove2.me/submissions/addb8880-a7dd-468b-9a57-a795d21f7156

import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_boundedVariation_min_one_abs_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_ae_continuous_on_compact_of_standing_bv_C1
import Theorems.Thm_AvramDividend_Classical_continuousWithinAt_integral_of_integrable_uniform_bound
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Restrict

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- BV C1 jump-generator continuity follows from a uniform first-order envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a))
    (hlinear : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y ∈ Iio (0 : ℝ),
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * min 1 |y|) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ y : ℝ, SpectrallyNegativeLevy.generatorIntegrand W x y
          ∂(X.ν.restrict (Iio 0)))
      (Icc l u) := by
  let μ : Measure ℝ := X.ν.restrict (Iio 0)
  obtain ⟨C, hC, hCb⟩ := hlinear
  have hmin : Integrable (fun y : ℝ => min 1 |y|) μ := by
    exact boundedVariation_min_one_abs_integrable X hbv
  have hbound_int : Integrable (fun y : ℝ => C * min 1 |y|) μ :=
    hmin.const_mul C
  have hmeas : ∀ x ∈ Icc l u,
      AEStronglyMeasurable
        (SpectrallyNegativeLevy.generatorIntegrand W x) μ := by
    intro x hx
    exact scaleFunction_generatorIntegrand_aestronglyMeasurable
      X q W hW x
  have hbound : ∀ x ∈ Icc l u,
      ∀ᵐ y ∂μ, ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
        C * min 1 |y| := by
    intro x hx
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := X.ν) measurableSet_Iio] with y hy
    exact hCb x hx y hy
  have hjump := scaleFunction_generatorIntegrand_ae_continuous_on_compact_of_standing_bv_C1
    X hX hbv q W hW a l u hl hlu hu hC1
  intro x hx
  exact continuousWithinAt_integral_of_integrable_uniform_bound
    μ (Icc l u)
    (fun z y => SpectrallyNegativeLevy.generatorIntegrand W z y)
    (fun y => C * min 1 |y|) x hx
    hmeas hbound hbound_int (hjump x hx)
