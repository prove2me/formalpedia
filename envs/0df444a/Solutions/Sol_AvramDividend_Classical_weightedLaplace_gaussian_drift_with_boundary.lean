-- Prove2me | solution 1 for AvramDividend.Classical.weightedLaplace_gaussian_drift_with_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:38:27.4003+00:00
-- url     : https://prove2.me/submissions/197e6537-bc4b-4373-b7dd-98d7afa02c49

import Mathlib
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_derivative_with_origin_boundary
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_second_derivative_with_boundary

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ) (θ σ c : ℝ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hcont1 : ContinuousWithinAt (deriv W) (Ici (0 : ℝ)) 0)
    (hderiv1 : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (deriv W) (deriv (deriv W) x) x)
    (hWint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)))
    (hDint : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * deriv W x) (Ioi (0 : ℝ)))
    (hD2int : IntegrableOn (fun x : ℝ =>
       Real.exp (-(θ * x)) * deriv (deriv W) x) (Ioi (0 : ℝ))) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) *
         ((σ ^ 2 / 2) * deriv (deriv W) x + c * deriv W x)) =
      ((σ ^ 2 / 2) * θ ^ 2 + c * θ) *
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) -
       ((σ ^ 2 / 2) * θ + c) * W 0 -
       (σ ^ 2 / 2) * deriv W 0 := by
  have h1 := weightedLaplace_derivative_with_origin_boundary
    W θ hcont hderiv hWint hDint
  have h2 := weightedLaplace_second_derivative_with_boundary
    W θ hcont hderiv hcont1 hderiv1 hWint hDint hD2int
  have hD2 : IntegrableOn
      (fun x : ℝ =>
        (σ ^ 2 / 2) *
          (Real.exp (-(θ * x)) * deriv (deriv W) x)) (Ioi (0 : ℝ)) :=
    hD2int.const_mul (σ ^ 2 / 2)
  have hD : IntegrableOn
      (fun x : ℝ =>
        c * (Real.exp (-(θ * x)) * deriv W x)) (Ioi (0 : ℝ)) :=
    hDint.const_mul c
  calc
    (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          ((σ ^ 2 / 2) * deriv (deriv W) x + c * deriv W x)) =
        ∫ x in Ioi (0 : ℝ),
          (σ ^ 2 / 2) *
             (Real.exp (-(θ * x)) * deriv (deriv W) x) +
          c * (Real.exp (-(θ * x)) * deriv W x) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
    _ = (σ ^ 2 / 2) *
          (∫ x in Ioi (0 : ℝ),
            Real.exp (-(θ * x)) * deriv (deriv W) x) +
        c * (∫ x in Ioi (0 : ℝ),
            Real.exp (-(θ * x)) * deriv W x) := by
          rw [integral_add hD2 hD, integral_const_mul, integral_const_mul]
    _ = ((σ ^ 2 / 2) * θ ^ 2 + c * θ) *
          (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) -
        ((σ ^ 2 / 2) * θ + c) * W 0 -
        (σ ^ 2 / 2) * deriv W 0 := by
          rw [h1, h2]
          ring
