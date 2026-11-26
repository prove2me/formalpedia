-- Prove2me | solution 1 for CollatzEndpointTransport.OptimizedLinearPullback.tolerance_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:00:40.681833+00:00
-- url     : https://prove2.me/submissions/50b67607-b7b3-4f2e-9ad2-c6772f047569

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.OptimizedLinearPullback
open scoped Real Topology
noncomputable section
namespace CollatzEndpointTransport.OptimizedLinearPullback
theorem _root_.solution
    {kappa t : ℝ}
    (hk : KappaAdmissible kappa)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    2 * (kappa * t) + (kappa * t) ^ 2 ≤ t := by
  have ht2 : t ^ 2 ≤ t := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hk20 : 0 ≤ kappa ^ 2 := sq_nonneg kappa
  have hquad : kappa ^ 2 * t ^ 2 ≤ kappa ^ 2 * t :=
    mul_le_mul_of_nonneg_left ht2 hk20
  have hcoef : (2 * kappa + kappa ^ 2) * t ≤ t :=
    mul_le_of_le_one_left ht0 hk.2.le
  nlinarith
end CollatzEndpointTransport.OptimizedLinearPullback
