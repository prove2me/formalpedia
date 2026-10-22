-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_laplaceExponent_esscher_shift_unit_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:58:59.4069+00:00
-- url     : https://prove2.me/submissions/b08bd56c-215e-47a3-b394-490f6c128cb8

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_gaussian_laplaceExponent_inclusive_drift_adjusted
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_esscher_shift_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- Gaussian Esscher shifting for the actual signed-jump Lévy exponent,
including the exact drift correction from a possible unit-magnitude atom. -/
theorem solution (c σ φ θ : ℝ) (ν : Measure ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2))
        ∂(ν.map (fun y : ℝ => -y))) < ⊤) :
    laplaceExponent c σ ν (φ + θ) - laplaceExponent c σ ν φ =
      θ * (c - (ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
        σ ^ 2 * φ +
        (∫ z in Ioi (0 : ℝ),
          (if z ≤ 1 then z else 0) -
            z * Real.exp (-φ * z) ∂(ν.map (fun y : ℝ => -y)))) +
        (σ ^ 2 / 2) * θ ^ 2 +
          (∫ z in Ioi (0 : ℝ),
            Real.exp (-φ * z) *
              (Real.exp (-θ * z) - 1 + θ * z)
                ∂(ν.map (fun y : ℝ => -y))) := by
  let μ : Measure ℝ := ν.map (fun y : ℝ => -y)
  let b : ℝ := c - μ.real ({1} : Set ℝ)
  let a : ℝ := σ ^ 2 / 2
  have hφθ : 0 ≤ φ + θ := add_nonneg hφ.le hθ
  have hleft :=
    gaussian_laplaceExponent_inclusive_drift_adjusted
      c σ (φ + θ) ν hφθ hlevy
  have hright :=
    gaussian_laplaceExponent_inclusive_drift_adjusted
      c σ φ ν hφ.le hlevy
  have hshift :=
    gaussian_levy_esscher_shift_real μ b a φ θ hφ hθ hlevy
  calc
    laplaceExponent c σ ν (φ + θ) - laplaceExponent c σ ν φ =
        (b * (φ + θ) + a * (φ + θ) ^ 2 +
          (∫ z in Ioi (0 : ℝ),
            Real.exp (-(φ + θ) * z) - 1 +
              (φ + θ) * (if z ≤ 1 then z else 0) ∂μ)) -
          (b * φ + a * φ ^ 2 +
            (∫ z in Ioi (0 : ℝ),
              Real.exp (-φ * z) - 1 +
                φ * (if z ≤ 1 then z else 0) ∂μ)) := by
      rw [hleft, hright]
      dsimp [b, a, μ]
      ring
    _ = θ * (b + 2 * a * φ +
          (∫ z in Ioi (0 : ℝ),
            (if z ≤ 1 then z else 0) -
              z * Real.exp (-φ * z) ∂μ)) +
          a * θ ^ 2 +
            (∫ z in Ioi (0 : ℝ),
              Real.exp (-φ * z) *
                (Real.exp (-θ * z) - 1 + θ * z) ∂μ) := hshift
    _ = _ := by
      dsimp [b, a, μ]
      ring
