-- Prove2me | solution 1 for CollatzEndpointTransport.OptimizedLinearPullback.hasDerivAt_psi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:44.358551+00:00
-- url     : https://prove2.me/submissions/d3f29c92-4132-49bf-9ae0-14c7c3975560

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_zero
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_inner_pos
attribute [local simp] CollatzEndpointTransport.OptimizedLinearPullback.psi_zero

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.OptimizedLinearPullback
open scoped Real Topology
noncomputable section
namespace CollatzEndpointTransport.OptimizedLinearPullback
theorem _root_.solution (D : ℝ) :
    HasDerivAt psi
      (Real.log 3 * Real.exp (-D * Real.log 3) /
        (1 + Real.exp (-D * Real.log 3))) D := by
  have hlin :
      HasDerivAt (fun x : ℝ => -x * Real.log 3) (-Real.log 3) D := by
    simpa using (hasDerivAt_id D).neg.mul_const (Real.log 3)
  have hexp :
      HasDerivAt (fun x : ℝ => Real.exp (-x * Real.log 3))
        ((-Real.log 3) * Real.exp (-D * Real.log 3)) D := by
    simpa [mul_comm] using hlin.exp
  have hinner :
      HasDerivAt
        (fun x : ℝ => (1 + Real.exp (-x * Real.log 3)) / 2)
        (((-Real.log 3) * Real.exp (-D * Real.log 3)) / 2) D := by
    simpa using (hasDerivAt_const D 1).add hexp |>.div_const 2
  have hlog :=
    hinner.log (ne_of_gt (psi_inner_pos D))
  have hderiv :
      -((((-Real.log 3) * Real.exp (-D * Real.log 3)) / 2) /
          ((1 + Real.exp (-D * Real.log 3)) / 2)) =
        Real.log 3 * Real.exp (-D * Real.log 3) /
          (1 + Real.exp (-D * Real.log 3)) := by
    field_simp [ne_of_gt (psi_inner_pos D)]
  change HasDerivAt
    (-fun x : ℝ => Real.log ((1 + Real.exp (-x * Real.log 3)) / 2))
    (Real.log 3 * Real.exp (-D * Real.log 3) /
      (1 + Real.exp (-D * Real.log 3))) D
  rw [← hderiv]
  exact hlog.neg
end CollatzEndpointTransport.OptimizedLinearPullback
