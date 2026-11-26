-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.realReverseMomentTerm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:43:33.546155+00:00
-- url     : https://prove2.me/submissions/65f88d9b-9f77-4dee-a086-976537fa95ca

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
    (theta : ℝ) {N : ℕ} (c : Composition N) (r : ℕ) :
    0 ≤ realReverseMomentTerm theta c r := by
  unfold realReverseMomentTerm
  positivity
end CollatzEndpointTransport.FixedTotal
