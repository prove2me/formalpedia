-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.binomialCenterDistance_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:45.191798+00:00
-- url     : https://prove2.me/submissions/3f3534ee-bbab-4144-96dc-f6abcf2b2cc9

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 200000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {H k : ℕ} (hk : k ≤ H) :
    binomialCenterDistance H k ≤ H := by
  unfold binomialCenterDistance
  split_ifs <;> omega
end CollatzEndpointTransport.FixedTotal
