-- Prove2me | solution 1 for AvramDividend.Classical.weightedLaplace_gaussian_drift_iteratedDeriv_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:13:06.065783+00:00
-- url     : https://prove2.me/submissions/1052b4d5-e46a-465f-854b-eeffd32dc032

import Mathlib
import Theorems.Thm_AvramDividend_Classical_iteratedDeriv_two_eq_deriv_deriv
import Theorems.Thm_AvramDividend_Classical_weightedLaplace_gaussian_drift_with_boundary

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
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
         ((σ ^ 2 / 2) * iteratedDeriv 2 W x + c * deriv W x)) =
      ((σ ^ 2 / 2) * θ ^ 2 + c * θ) *
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x) -
       ((σ ^ 2 / 2) * θ + c) * W 0 -
       (σ ^ 2 / 2) * deriv W 0 := by
  simpa only [iteratedDeriv_two_eq_deriv_deriv] using
    weightedLaplace_gaussian_drift_with_boundary W θ σ c
      hcont hderiv hcont1 hderiv1 hWint hDint hD2int
