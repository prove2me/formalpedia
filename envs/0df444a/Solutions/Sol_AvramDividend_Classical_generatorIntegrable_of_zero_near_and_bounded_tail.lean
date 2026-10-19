-- Prove2me | solution 1 for AvramDividend.Classical.generatorIntegrable_of_zero_near_and_bounded_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T05:55:30.010145+00:00
-- url     : https://prove2.me/submissions/356a8100-fce0-4533-9e40-9c37b9874f01

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory
open AvramDividend.Classical
open scoped NNReal ENNReal

-- Exact source-level candidate, independent of any unproved theorem.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (x δ M : ℝ)
    (hδ : 0 < δ)
    (hmeas : Measurable (SpectrallyNegativeLevy.generatorIntegrand f x))
    (hfinite : X.ν (Iic (-δ)) < ⊤)
    (hbound : ∀ y ∈ Iic (-δ),
      |SpectrallyNegativeLevy.generatorIntegrand f x y| ≤ M)
    (hzero : ∀ y, -δ < y → y < 0 →
      SpectrallyNegativeLevy.generatorIntegrand f x y = 0) :
    X.GeneratorIntegrable f x := by
  let g := SpectrallyNegativeLevy.generatorIntegrand f x
  have htail : IntegrableOn g (Iic (-δ)) X.ν := by
    apply IntegrableOn.of_bound hfinite (hmeas.aestronglyMeasurable.restrict) M
    filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
    simpa only [Real.norm_eq_abs] using hbound y hy
  have hvanish : ∀ y ∈ Iio (0 : ℝ) \ Iic (-δ), g y = 0 := by
    intro y hy
    exact hzero y (lt_of_not_ge hy.2) hy.1
  exact htail.of_forall_sdiff_eq_zero measurableSet_Iio hvanish