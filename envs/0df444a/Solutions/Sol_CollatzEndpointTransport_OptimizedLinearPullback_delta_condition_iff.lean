-- Prove2me | solution 1 for CollatzEndpointTransport.OptimizedLinearPullback.delta_condition_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:10.039956+00:00
-- url     : https://prove2.me/submissions/86e5846a-3a4f-47e9-b0cc-a1c1999e3423

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
    {q kappa transport d : ℝ}
    (hbeta : 0 < beta q kappa transport + 1) :
    d < delta q kappa transport ↔
      d * (beta q kappa transport + 1) < 1 := by
  unfold delta
  exact lt_div_iff₀ hbeta
end CollatzEndpointTransport.OptimizedLinearPullback
