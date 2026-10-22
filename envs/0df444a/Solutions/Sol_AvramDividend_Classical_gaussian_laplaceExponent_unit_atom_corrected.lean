-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_laplaceExponent_unit_atom_corrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:33:41.869816+00:00
-- url     : https://prove2.me/submissions/bf6c1b64-5406-460e-b6d1-e27858d7ba57

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_integrand_mirror
import Theorems.Thm_AvramDividend_Classical_gaussian_open_closed_truncation_atom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

/-- The signed-jump Lévy exponent equals the inclusive-cutoff Gaussian
jump magnitude formula after retaining the precise unit-atom correction. -/
theorem solution (c σ : ℝ) (ν : Measure ℝ) (θ : ℝ) :
    laplaceExponent c σ ν θ =
      c * θ + σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Iio (0 : ℝ),
          (Real.exp (-θ * (-y)) - 1 +
            θ * (if -y ≤ 1 then -y else 0)) -
              θ * (if -y = 1 then (1 : ℝ) else 0) ∂ν) := by
  unfold laplaceExponent
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
  calc
    Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y =
      Real.exp (-θ * (-y)) - 1 +
        θ * (if -y < 1 then -y else 0) :=
      gaussian_negative_jump_integrand_mirror θ y hy
    _ = (Real.exp (-θ * (-y)) - 1 +
        θ * (if -y ≤ 1 then -y else 0)) -
          θ * (if -y = 1 then (1 : ℝ) else 0) := by
      rw [gaussian_open_closed_truncation_atom (-y)]
      ring
