-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_laplaceExponent_signed_magnitude_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:33:45.323807+00:00
-- url     : https://prove2.me/submissions/afc338c9-8e24-4272-a78c-6e1306a93f64

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_integrand_mirror

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

/-- The actual signed-jump Lévy exponent has an exact positive-magnitude
integrand while retaining the canonical strict truncation at one. -/
theorem solution (c σ : ℝ) (ν : Measure ℝ) (θ : ℝ) :
    laplaceExponent c σ ν θ =
      c * θ + σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Iio (0 : ℝ),
          Real.exp (-θ * (-y)) - 1 +
            θ * (if -y < 1 then -y else 0) ∂ν) := by
  unfold laplaceExponent
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
  exact gaussian_negative_jump_integrand_mirror θ y hy
