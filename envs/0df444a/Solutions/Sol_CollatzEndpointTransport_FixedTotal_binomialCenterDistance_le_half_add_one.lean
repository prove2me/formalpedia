-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.binomialCenterDistance_le_half_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:44:26.03636+00:00
-- url     : https://prove2.me/submissions/afe57a74-39bf-4677-9483-6a49403b4c17

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
    binomialCenterDistance H k ≤ H / 2 + 1 := by
  unfold binomialCenterDistance
  split_ifs <;> omega
end CollatzEndpointTransport.FixedTotal
