-- Prove2me | solution 1 for CollatzEndpointTransport.OptimizedLinearPullback.tendsto_normalizedRate_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:59.431402+00:00
-- url     : https://prove2.me/submissions/204147c0-7466-4b34-9f44-c52ff10a1d45

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_zero
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_tendsto_psi_div_zero_right
attribute [local simp] CollatzEndpointTransport.OptimizedLinearPullback.psi_zero

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.OptimizedLinearPullback
open scoped Real Topology
noncomputable section
namespace CollatzEndpointTransport.OptimizedLinearPullback
theorem _root_.solution :
    Filter.Tendsto
      (fun D : ℝ => psi D / (3 * Real.log 2 * D))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds asymptoticRateLimit) := by
  have h :=
    tendsto_psi_div_zero_right.div_const (3 * Real.log 2)
  have hfun :
      (fun D : ℝ => psi D / (3 * Real.log 2 * D)) =
        (fun D : ℝ => (psi D / D) / (3 * Real.log 2)) := by
    funext D
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hlim :
      Real.log 3 / 2 / (3 * Real.log 2) = asymptoticRateLimit := by
    unfold asymptoticRateLimit
    ring_nf
  rw [hfun]
  rw [← hlim]
  exact h
end CollatzEndpointTransport.OptimizedLinearPullback
