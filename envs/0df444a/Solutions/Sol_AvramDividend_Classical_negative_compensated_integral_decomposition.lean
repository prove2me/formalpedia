-- Prove2me | solution 1 for AvramDividend.Classical.negative_compensated_integral_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:33:09.487036+00:00
-- url     : https://prove2.me/submissions/0701b9a7-132d-4873-98fc-7b869cd0a937

import Mathlib

open MeasureTheory Filter

theorem AvramDividend.Classical.negative_compensated_integral_decomposition
    (ν : Measure ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hneg : ∀ᵐ y ∂ν, y < 0)
    (hfirst : Integrable (fun y : ℝ => |y|) ν)
    (hres : Integrable (fun y : ℝ =>
      (1 - Real.exp (θ * y)) / θ) ν) :
    (∫ y : ℝ,
      (Real.exp (θ * y) - 1 - θ * y) / θ ∂ν) =
      (∫ y : ℝ, |y| ∂ν) -
        (∫ y : ℝ, (1 - Real.exp (θ * y)) / θ ∂ν) := by
  calc
    _ = ∫ y : ℝ, |y| - (1 - Real.exp (θ * y)) / θ ∂ν := by
      apply integral_congr_ae
      filter_upwards [hneg] with y hy
      rw [abs_of_neg hy]
      field_simp
      <;> ring
    _ = _ := integral_sub hfirst hres

theorem solution
    (ν : Measure ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hneg : ∀ᵐ y ∂ν, y < 0)
    (hfirst : Integrable (fun y : ℝ => |y|) ν)
    (hres : Integrable (fun y : ℝ =>
      (1 - Real.exp (θ * y)) / θ) ν) :
    (∫ y : ℝ,
      (Real.exp (θ * y) - 1 - θ * y) / θ ∂ν) =
      (∫ y : ℝ, |y| ∂ν) -
        (∫ y : ℝ, (1 - Real.exp (θ * y)) / θ ∂ν) := AvramDividend.Classical.negative_compensated_integral_decomposition ν θ hθ hneg hfirst hres

#print axioms solution

