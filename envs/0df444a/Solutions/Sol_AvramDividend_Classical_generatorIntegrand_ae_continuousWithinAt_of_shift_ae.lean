-- Prove2me | solution 1 for AvramDividend.Classical.generatorIntegrand_ae_continuousWithinAt_of_shift_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:22:54.374798+00:00
-- url     : https://prove2.me/submissions/f4e6548b-2b5e-4bce-8be7-5356c82114aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_continuousAt_of_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ) (μ : Measure ℝ) (s : Set ℝ) (x : ℝ)
    (hWx : ContinuousAt W x)
    (hderiv : ContinuousAt (deriv W) x)
    (hshift : ∀ᵐ y ∂μ, ContinuousAt W (x + y)) :
    ∀ᵐ y ∂μ,
      ContinuousWithinAt
        (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand W z y)
        s x := by
  filter_upwards [hshift] with y hWxy
  exact (generatorIntegrand_continuousAt_of_continuous
    W x y hWx hWxy hderiv).continuousWithinAt
