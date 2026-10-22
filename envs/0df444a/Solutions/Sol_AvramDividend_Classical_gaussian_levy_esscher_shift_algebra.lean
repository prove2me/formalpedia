-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_levy_esscher_shift_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:09:12.709959+00:00
-- url     : https://prove2.me/submissions/121c29b5-018f-4d2e-916b-fa8a18618694

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exact Esscher-shift decomposition with an arbitrary Lévy truncation term. -/
theorem solution (φ θ z k : ℝ) :
    (Real.exp (-(φ + θ) * z) - 1 + (φ + θ) * k) -
        (Real.exp (-φ * z) - 1 + φ * k) =
      Real.exp (-φ * z) *
          (Real.exp (-θ * z) - 1 + θ * z) +
        θ * (k - z * Real.exp (-φ * z)) := by
  have hexp :
      Real.exp (-(φ + θ) * z) =
        Real.exp (-φ * z) * Real.exp (-θ * z) := by
    rw [show -(φ + θ) * z = -φ * z + -θ * z by ring]
    exact Real.exp_add _ _
  rw [hexp]
  ring
