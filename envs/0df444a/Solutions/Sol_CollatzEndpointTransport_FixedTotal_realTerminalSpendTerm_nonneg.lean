-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.realTerminalSpendTerm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:23.547258+00:00
-- url     : https://prove2.me/submissions/f98d55ba-f21d-4309-8e1a-7401a05fe84f

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (theta : ℝ) (r D : ℕ) :
    0 ≤ realTerminalSpendTerm theta r D := by
  unfold realTerminalSpendTerm
  positivity
end CollatzEndpointTransport.FixedTotal
