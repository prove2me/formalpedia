-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_shellBad_collatzPullback_eq_sourceEndpointBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:29:40.306392+00:00
-- url     : https://prove2.me/submissions/f868e7bf-07b7-4a0a-aa3d-4cefff60760c

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalShellCoding
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceEndpointBad_eq_endpointShellBad
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_shellBad_collatzPullback_eq_endpointShellBad

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (S : Set ℕ) (M : ℕ) :
    (QuantitativeDensity.shellBad
        (QuantitativeDensity.collatzPullback S) M).card =
      (sourceEndpointBad S M).card := by
  rw [shellBad_collatzPullback_eq_endpointShellBad,
    card_sourceEndpointBad_eq_endpointShellBad]
end CollatzEndpointTransport.FixedTotal
