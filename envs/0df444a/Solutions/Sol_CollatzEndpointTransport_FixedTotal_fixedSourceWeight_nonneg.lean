-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedSourceWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:37:31.565145+00:00
-- url     : https://prove2.me/submissions/3a4f21bd-9230-4885-b9ec-934418138baf

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
    (N s : ℕ) :
    0 ≤ fixedSourceWeight N s := by
  unfold fixedSourceWeight
  positivity
end CollatzEndpointTransport.FixedTotal
