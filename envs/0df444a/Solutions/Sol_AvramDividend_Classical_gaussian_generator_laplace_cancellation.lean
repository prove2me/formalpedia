-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_generator_laplace_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:27:12.137587+00:00
-- url     : https://prove2.me/submissions/70e90380-65b5-4cb5-a1ca-f69cc60d4271

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    (d c θ q ψ J η : ℝ)
    (hψ : ψ = d * θ ^ 2 + c * θ + J)
    (hqψ : q < ψ) (horigin : d * η = 1) :
    (d * θ ^ 2 + c * θ + J - q) * (ψ - q)⁻¹ -
      d * η = 0 := by
  have hne : ψ - q ≠ 0 := sub_ne_zero.mpr (ne_of_gt hqψ)
  rw [← hψ, horigin]
  field_simp [hne]
  ring
