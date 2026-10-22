-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_laplaceExponent_pushforward_unit_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:53:58.437733+00:00
-- url     : https://prove2.me/submissions/4d5ca048-cfeb-43f4-9bbf-e5d218963c87

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_laplaceExponent_positive_magnitude
import Theorems.Thm_AvramDividend_Classical_gaussian_open_closed_truncation_atom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

/-- The mission's negative-jump Laplace exponent is the inclusive-cutoff
positive-magnitude exponent with its exact unit-magnitude atom correction. -/
theorem solution (c σ θ : ℝ) (ν : Measure ℝ) :
    laplaceExponent c σ ν θ =
      c * θ + σ ^ 2 * θ ^ 2 / 2 +
        (∫ z in Ioi (0 : ℝ),
          (Real.exp (-θ * z) - 1 +
            θ * (if z ≤ 1 then z else 0)) -
              θ * (if z = 1 then (1 : ℝ) else 0)
              ∂(ν.map (fun y : ℝ => -y))) := by
  rw [gaussian_laplaceExponent_positive_magnitude]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    change Real.exp (-θ * z) - 1 +
        θ * (if z < 1 then z else 0) =
      (Real.exp (-θ * z) - 1 +
        θ * (if z ≤ 1 then z else 0)) -
          θ * (if z = 1 then (1 : ℝ) else 0)
    rw [gaussian_open_closed_truncation_atom z]
    ring)
