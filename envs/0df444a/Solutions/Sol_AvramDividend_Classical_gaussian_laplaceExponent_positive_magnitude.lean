-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_laplaceExponent_positive_magnitude
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:42:21.753648+00:00
-- url     : https://prove2.me/submissions/51ea43cb-a9c9-46ec-b073-22a7213aee23

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_gaussian_laplaceExponent_signed_magnitude_bridge
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_integral_pushforward

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

/-- The actual spectrally negative Lévy–Khintchine exponent is exactly
the positive jump-magnitude exponent for the negation pushforward,
with the canonical strict truncation preserved. -/
theorem solution (c σ θ : ℝ) (ν : Measure ℝ) :
    laplaceExponent c σ ν θ =
      c * θ + σ ^ 2 * θ ^ 2 / 2 +
        (∫ z in Ioi (0 : ℝ),
          Real.exp (-θ * z) - 1 +
            θ * (if z < 1 then z else 0)
              ∂(ν.map (fun y : ℝ => -y))) := by
  let F : ℝ → ℝ := fun z =>
    Real.exp (-θ * z) - 1 +
      θ * (if z < 1 then z else 0)
  have hif : Measurable (fun z : ℝ =>
      if z < 1 then z else 0) := by
    have hs : MeasurableSet {z : ℝ | z < 1} :=
      measurableSet_lt measurable_id
        (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ)))
    exact measurable_id.ite hs measurable_const
  have hF : Measurable F := by
    have he : Measurable (fun z : ℝ =>
        Real.exp (-θ * z) - 1) := by fun_prop
    exact he.add (measurable_const.mul hif)
  have hbridge :=
    gaussian_laplaceExponent_signed_magnitude_bridge c σ ν θ
  have htransport :=
    gaussian_negative_jump_integral_pushforward ν F hF
  calc
    _ = c * θ + σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Iio (0 : ℝ), F (-y) ∂ν) := by
      simpa only [F] using hbridge
    _ = c * θ + σ ^ 2 * θ ^ 2 / 2 +
        (∫ z in Ioi (0 : ℝ), F z
          ∂(ν.map (fun y : ℝ => -y))) := by
      rw [htransport]
    _ = _ := rfl
