-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p3_bv_generator_integrable_of_first_moment_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:08:57.887616+00:00
-- url     : https://prove2.me/submissions/4293a94a-ffeb-499b-9eb4-a8041ce10242

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_min_one_abs_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- In the bounded-variation regime a measurable compensated jump
integrand dominated by a multiple of min(1,|y|) belongs to the
actual original generator domain. No continuity or monotonicity
of the payoff is required. Unpublished, uncompiled P3 draft. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (f : ℝ → ℝ) (hfmeas : Measurable f) (x : ℝ)
    (henv : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Iio (0 : ℝ),
        ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
          C * min 1 |y|) :
    X.GeneratorIntegrable f x := by
  let μ : Measure ℝ := X.ν.restrict (Iio 0)
  obtain ⟨C, hC, hCb⟩ := henv
  have hmin : Integrable (fun y : ℝ => min 1 |y|) μ :=
    boundedVariation_min_one_abs_integrable X hbv
  have hmajor : Integrable (fun y : ℝ => C * min 1 |y|) μ :=
    hmin.const_mul C
  have hshift : Measurable (fun y : ℝ => f (x + y)) :=
    hfmeas.comp (measurable_const.add measurable_id)
  have hind : Measurable
      (fun y : ℝ =>
        (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) :=
    measurable_const.indicator measurableSet_Ioo
  have hmeas :
      AEStronglyMeasurable
        (SpectrallyNegativeLevy.generatorIntegrand f x) μ := by
    have hm : Measurable
        (SpectrallyNegativeLevy.generatorIntegrand f x) := by
      unfold SpectrallyNegativeLevy.generatorIntegrand
      exact (hshift.sub measurable_const).sub
        ((measurable_const.mul measurable_id).mul hind)
    exact hm.aestronglyMeasurable
  have hdom : Integrable
      (SpectrallyNegativeLevy.generatorIntegrand f x) μ := by
    apply hmajor.mono' hmeas
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := X.ν) measurableSet_Iio] with y hy
    have hmin_nonneg : 0 ≤ min 1 |y| :=
      le_min (by norm_num) (abs_nonneg y)
    have hmajor_nonneg : 0 ≤ C * min 1 |y| :=
      mul_nonneg hC hmin_nonneg
    simpa only [Real.norm_eq_abs, abs_of_nonneg hmajor_nonneg] using
      hCb y hy
  change IntegrableOn
    (SpectrallyNegativeLevy.generatorIntegrand f x)
    (Iio (0 : ℝ)) X.ν
  exact hdom
