-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.actualCriticalEndpointInformation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:46:44.434801+00:00
-- url     : https://prove2.me/submissions/80b6aa3c-e1fb-44a1-bdda-5ed350751566

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualCriticalEndpointInformation_eq
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_criticalEndpointInformation_le


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) (hM : 1 ≤ M) :
    actualCriticalEndpointInformation M ≤
      9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M := by
  rw [actualCriticalEndpointInformation_eq]
  exact criticalEndpointInformation_le M hM
end CollatzEndpointTransport.FixedTotal
