-- Prove2me | solution 1 for AvramDividend.Classical.weightedLaplace_second_derivative_with_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:36:54.309409+00:00
-- url     : https://prove2.me/submissions/49ec23e7-8bd1-4375-a227-0135700a4e9a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_derivative_with_origin_boundary

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ) (θ : ℝ)
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
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * deriv (deriv W) x) =
      θ ^ 2 * (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) -
        θ * W 0 - deriv W 0 := by
  have h1 := weightedLaplace_derivative_with_origin_boundary
    W θ hcont hderiv hWint hDint
  have h2 := weightedLaplace_derivative_with_origin_boundary
    (deriv W) θ hcont1 hderiv1 hDint hD2int
  calc
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) * deriv (deriv W) x) =
        θ * (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) * deriv W x) - deriv W 0 := h2
    _ = θ ^ 2 * (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ * x)) * W x) - θ * W 0 - deriv W 0 := by
            rw [h1]
            ring
