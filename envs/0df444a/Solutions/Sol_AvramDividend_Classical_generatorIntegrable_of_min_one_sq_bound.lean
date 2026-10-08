-- Prove2me | solution 1 for AvramDividend.Classical.generatorIntegrable_of_min_one_sq_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T06:20:05.128019+00:00
-- url     : https://prove2.me/submissions/97c2b169-758d-4289-a648-1ab79d9ce097

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

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
    (f : ℝ → ℝ) (x C : ℝ)
    (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable
      (SpectrallyNegativeLevy.generatorIntegrand f x)
      (X.ν.restrict (Iio 0)))
    (hbound : ∀ y ∈ Iio (0 : ℝ),
      |SpectrallyNegativeLevy.generatorIntegrand f x y| ≤
        C * min 1 (y ^ 2)) :
    X.GeneratorIntegrable f x := by
  have hbase_meas :
      AEStronglyMeasurable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by
    exact
      (continuous_const.min (continuous_id.pow 2)).aestronglyMeasurable
  have hbase_nonneg :
      0 ≤ᵐ[X.ν] (fun y : ℝ => min 1 (y ^ 2)) := by
    filter_upwards with y
    positivity
  have hbase :
      Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν := by
    refine (lintegral_ofReal_ne_top_iff_integrable
      hbase_meas hbase_nonneg).mp ?_
    exact ne_of_lt X.ν_integrable
  have hdom :
      IntegrableOn (fun y : ℝ => C * min 1 (y ^ 2))
        (Iio (0 : ℝ)) X.ν := by
    exact (hbase.const_mul C).integrableOn
  change Integrable
    (SpectrallyNegativeLevy.generatorIntegrand f x)
    (X.ν.restrict (Iio (0 : ℝ)))
  refine hdom.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
  simpa only [Real.norm_eq_abs] using hbound y hy
