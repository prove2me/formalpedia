-- Prove2me | solution 1 for FeynmanKac.discounted_gradient_ito_integral_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T08:47:05.339085+00:00
-- url     : https://prove2.me/submissions/5642fd47-9652-4def-aab5-7f74abbf5fe1

import Definitions.Def_FeynmanKac_AdmissibleDiscountedGradient
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ)
    (h : m.AdmissibleDiscountedGradient u) :
    Martingale
      (fun r ω =>
        m.discountedGradientItoIntegral u h (m.initialTime + r) ω)
      m.filtration P := by
  simpa [FeynmanKac.BoundedDiffusionModel.discountedGradientItoIntegral,
    add_sub_cancel_left] using
      (LevyStochCalc.Brownian.Ito.martingale_stochasticIntegralBrownian
        (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
        (m.discountedGradientIntegrand u) h.1 h.2.1 h.2.2)
