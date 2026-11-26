-- Prove2me | solution 1 for CollatzEndpointTransport.OptimizedLinearPullback.psi_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:14:37.101244+00:00
-- url     : https://prove2.me/submissions/e65ffe0d-546b-419b-8eed-0a2fac492ea1

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_inner_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.OptimizedLinearPullback
open scoped Real Topology
noncomputable section
namespace CollatzEndpointTransport.OptimizedLinearPullback
theorem _root_.solution {D : ℝ} (hD : 0 < D) :
    0 < psi D := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hexp :
      Real.exp (-D * Real.log 3) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hinner :
      (1 + Real.exp (-D * Real.log 3)) / 2 < 1 := by
    linarith
  unfold psi
  exact neg_pos.mpr (Real.log_neg (psi_inner_pos D) hinner)
end CollatzEndpointTransport.OptimizedLinearPullback
