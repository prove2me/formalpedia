-- Prove2me | solution 1 for AvramDividend.Classical.negative_compensated_integral_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T22:32:07.075559+00:00
-- url     : https://prove2.me/submissions/22be9b6a-9799-43a2-acb3-819c4635d93e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exp_negative_compensated_secant_mono

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open AvramDividend.Classical

theorem solution
    (ν : Measure ℝ) (θ₁ θ₂ : ℝ)
    (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ₂)
    (hneg : ∀ᵐ y ∂ν, y < 0)
    (hi₁ : Integrable (fun y : ℝ =>
      (Real.exp (θ₁ * y) - 1 - θ₁ * y) / θ₁) ν)
    (hi₂ : Integrable (fun y : ℝ =>
      (Real.exp (θ₂ * y) - 1 - θ₂ * y) / θ₂) ν) :
    (∫ y : ℝ, (Real.exp (θ₁ * y) - 1 - θ₁ * y) / θ₁ ∂ν) ≤
      ∫ y : ℝ, (Real.exp (θ₂ * y) - 1 - θ₂ * y) / θ₂ ∂ν := by
  apply integral_mono_ae hi₁ hi₂
  filter_upwards [hneg] with y hy
  exact exp_negative_compensated_secant_mono y θ₁ θ₂ hy hθ₁ hθ
