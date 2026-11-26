-- Prove2me | solution 1 for CollatzEndpointTransport.OptimizedLinearPullback.linearRecurrence_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:00:52.363002+00:00
-- url     : https://prove2.me/submissions/e3b3dc60-c494-42eb-99d0-cea9ddc5dc7c

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_zero
attribute [local simp] CollatzEndpointTransport.OptimizedLinearPullback.psi_zero

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.OptimizedLinearPullback
open scoped Real Topology
noncomputable section
namespace CollatzEndpointTransport.OptimizedLinearPullback
theorem _root_.solution
    (c D0 : ℝ) (D : ℕ → ℝ)
    (hD0 : D 0 = D0)
    (hstep : ∀ j, D (j + 1) = c * D j) :
    ∀ j, D j = c ^ j * D0 := by
  intro j
  induction j with
  | zero => simpa using hD0
  | succ j ih =>
      rw [hstep, ih, pow_succ]
      ring
end CollatzEndpointTransport.OptimizedLinearPullback
