-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_volterra_transform_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T22:37:54.972295+00:00
-- url     : https://prove2.me/submissions/8ead9949-02c2-490f-befc-161678e8e5c5

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Algebraic core of the Gaussian scale-function Volterra Laplace transform. -/
theorem solution
    (δ d θ Rhat F : ℝ)
    (htransform :
      (δ * θ ^ 2 + d * θ + θ ^ 2 * Rhat) * F = 1) :
    θ ^ 2 * (δ * F + Rhat * F) + θ * (d * F) = 1 := by
  calc
    θ ^ 2 * (δ * F + Rhat * F) + θ * (d * F) =
        (δ * θ ^ 2 + d * θ + θ ^ 2 * Rhat) * F := by
      ring
    _ = 1 := htransform
