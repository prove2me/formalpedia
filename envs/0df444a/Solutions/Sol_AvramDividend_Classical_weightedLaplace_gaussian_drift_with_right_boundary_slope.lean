-- Prove2me | solution 1 for AvramDividend.Classical.weightedLaplace_gaussian_drift_with_right_boundary_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:44:55.473069+00:00
-- url     : https://prove2.me/submissions/82e1ea41-f480-4d9b-877c-667aeec8241a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_derivative_with_origin_boundary
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_second_derivative_with_right_boundary_slope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ) (θ σ c η : ℝ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x)
    (hDlim : Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 η))
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
       (σ ^ 2 / 2) * η := by
  have h1 := weightedLaplace_derivative_with_origin_boundary
    W θ hcont hderiv hWint hDint
  have h2 := weightedLaplace_second_derivative_with_right_boundary_slope
    W θ η hcont hderiv hDlim hderiv1 hWint hDint hD2int
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
        (σ ^ 2 / 2) * η := by
          rw [h1, h2]
          ring
