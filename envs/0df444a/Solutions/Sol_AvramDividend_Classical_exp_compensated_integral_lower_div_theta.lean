-- Prove2me | solution 1 for AvramDividend.Classical.exp_compensated_integral_lower_div_theta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T21:45:29.883906+00:00
-- url     : https://prove2.me/submissions/1e078831-8b97-4eb8-9170-6af06052c0d6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exp_compensated_integral_lower_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

theorem solution
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (θ : ℝ) (hθ : 0 < θ)
    (hneg : ∀ᵐ y ∂ν, y ≤ 0)
    (hyint : Integrable (fun y : ℝ => y) ν) :
    (∫ y : ℝ, |y| ∂ν) -
      (∫ y : ℝ, (1 : ℝ) ∂ν) / θ ≤
      (∫ y : ℝ, (Real.exp (θ * y) - 1 - θ * y) ∂ν) / θ := by
  have hmain :=
    exp_compensated_integral_lower_finite ν θ (le_of_lt hθ) hneg hyint
  have hleft :
      (∫ y : ℝ, θ * |y| - 1 ∂ν) =
        θ * (∫ y : ℝ, |y| ∂ν) -
          (∫ y : ℝ, (1 : ℝ) ∂ν) := by
    rw [integral_sub (hyint.abs.const_mul θ) (integrable_const (1 : ℝ))]
    rw [integral_const_mul]
  rw [hleft] at hmain
  apply (le_div_iff₀ hθ).2
  calc
    ((∫ y : ℝ, |y| ∂ν) -
        (∫ y : ℝ, (1 : ℝ) ∂ν) / θ) * θ =
        θ * (∫ y : ℝ, |y| ∂ν) -
          (∫ y : ℝ, (1 : ℝ) ∂ν) := by
      field_simp [ne_of_gt hθ]
    _ ≤ ∫ y : ℝ, (Real.exp (θ * y) - 1 - θ * y) ∂ν := hmain
