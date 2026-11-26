-- Prove2me | solution 1 for CollatzEndpointTransport.OptimizedLinearPullback.kappa_mul_cq_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:00:51.30249+00:00
-- url     : https://prove2.me/submissions/a1ffb529-2d29-486f-b509-ccbb43cf43fe

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
    {kappa q : ℝ} (hk : 0 < kappa) (hq : 0 < q) :
    kappa * cq kappa q * q =
      (q - QuantitativeDensity.a0) / 4 := by
  unfold cq
  field_simp [ne_of_gt hk, ne_of_gt hq]
end CollatzEndpointTransport.OptimizedLinearPullback
