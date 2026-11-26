-- Prove2me | solution 1 for CollatzEndpointTransport.OptimizedLinearPullback.tendsto_psi_div_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:47:29.806322+00:00
-- url     : https://prove2.me/submissions/4f1a5d98-85fb-424a-9fb1-207534bc0c4d

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_zero
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_hasDerivAt_psi
attribute [local simp] CollatzEndpointTransport.OptimizedLinearPullback.psi_zero

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.OptimizedLinearPullback
open scoped Real Topology
noncomputable section
namespace CollatzEndpointTransport.OptimizedLinearPullback
theorem _root_.solution :
    Filter.Tendsto (fun D : ℝ => psi D / D)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log 3 / 2)) := by
  have h :=
    (hasDerivAt_psi 0).tendsto_slope_zero_right
  convert h using 1 <;>
    norm_num [psi_zero, div_eq_mul_inv, mul_comm]
end CollatzEndpointTransport.OptimizedLinearPullback
