-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_shift_with_one_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:48:27.321382+00:00
-- url     : https://prove2.me/submissions/fb09a406-a387-4e26-b324-9c12965aee99

import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_esscher_shift_algebra
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- Exact Gaussian-plus-single-jump Esscher-shift exponent identity. -/
theorem solution (b a φ θ z k : ℝ) :
    (b * (φ + θ) + a * (φ + θ) ^ 2 +
        (Real.exp (-(φ + θ) * z) - 1 + (φ + θ) * k)) -
      (b * φ + a * φ ^ 2 +
        (Real.exp (-φ * z) - 1 + φ * k)) =
      θ * (b + 2 * a * φ + k - z * Real.exp (-φ * z)) +
        a * θ ^ 2 +
          Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z) := by
  calc
    _ =
      (b * (φ + θ) + a * (φ + θ) ^ 2) -
        (b * φ + a * φ ^ 2) +
          ((Real.exp (-(φ + θ) * z) - 1 + (φ + θ) * k) -
            (Real.exp (-φ * z) - 1 + φ * k)) := by ring
    _ = _ := by
      rw [gaussian_levy_esscher_shift_algebra φ θ z k]
      ring
