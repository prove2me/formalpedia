-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.natPow_rpow_eq_rpow_natPow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:36:42.068862+00:00
-- url     : https://prove2.me/submissions/c78dbe2e-8ce0-4525-812c-8e45798ea3c6

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (theta : ℝ) :
    (x ^ n) ^ theta = (x ^ theta) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx,
    mul_comm, Real.rpow_mul hx, Real.rpow_natCast]
end CollatzEndpointTransport.FixedTotal
