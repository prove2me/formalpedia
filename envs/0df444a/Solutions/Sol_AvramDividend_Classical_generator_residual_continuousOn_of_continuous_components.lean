-- Prove2me | solution 1 for AvramDividend.Classical.generator_residual_continuousOn_of_continuous_components
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:12:02.62999+00:00
-- url     : https://prove2.me/submissions/f73dcb85-ce01-418c-a3ce-3cd5fc7c5f1d

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
    (q : ℝ) (W : ℝ → ℝ) (s : Set ℝ)
    (hW : ContinuousOn W s)
    (hD : ContinuousOn (deriv W) s)
    (hD2 : ContinuousOn (iteratedDeriv 2 W) s)
    (hJ : ContinuousOn
      (fun x : ℝ =>
        ∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)
      s) :
    ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x) s := by
  unfold SpectrallyNegativeLevy.generator
  fun_prop
