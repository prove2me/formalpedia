-- Prove2me | solution 1 for AvramDividend.Classical.generatorIntegrable_of_min_sq_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:53:38.315498+00:00
-- url     : https://prove2.me/submissions/fed33944-5222-4424-9152-634c9d8a8296

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (x C : ℝ) (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable
      (SpectrallyNegativeLevy.generatorIntegrand f x)
      (X.ν.restrict (Iio 0)))
    (hbound : ∀ᵐ y ∂X.ν.restrict (Iio 0),
      ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
        C * min 1 (y ^ 2)) :
    X.GeneratorIntegrable f x := by
  change Integrable
    (SpectrallyNegativeLevy.generatorIntegrand f x)
    (X.ν.restrict (Iio 0))
  have hmin_meas :
      AEStronglyMeasurable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by
    fun_prop
  have hmin_nonneg :
      0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) := by
    filter_upwards with y
    positivity
  have hmin :
      Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by
    exact
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        hmin_meas hmin_nonneg).mp (ne_of_lt X.ν_integrable)
  have hdom_full :
      Integrable (fun y : ℝ => C * min 1 (y ^ 2)) X.ν := by
    exact hmin.const_mul C
  have hdom :
      Integrable (fun y : ℝ => C * min 1 (y ^ 2))
        (X.ν.restrict (Iio 0)) := by
    exact hdom_full.mono_measure (Measure.restrict_le_self)
  apply hdom.mono hmeas
  filter_upwards [hbound] with y hy
  have hmin0 : 0 ≤ min 1 (y ^ 2) := by positivity
  simpa only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hC, abs_of_nonneg hmin0] using hy
