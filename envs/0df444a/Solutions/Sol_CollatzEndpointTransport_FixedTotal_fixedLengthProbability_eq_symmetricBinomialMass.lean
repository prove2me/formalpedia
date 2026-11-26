-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedLengthProbability_eq_symmetricBinomialMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:50:21.481221+00:00
-- url     : https://prove2.me/submissions/6ff05604-d422-4edb-a644-6c9b6c9b5fcb

import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralAggregate
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} (hN : 0 < N) (hs : 0 < s) :
    fixedLengthProbability N s =
      symmetricBinomialMass (N - 1) (s - 1) := by
  unfold fixedLengthProbability symmetricBinomialMass
  rw [card_fixedSet N s hN hs]
end CollatzEndpointTransport.FixedTotal
