-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.binomialAnnulusWidth_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:44:02.99616+00:00
-- url     : https://prove2.me/submissions/de52a564-fd72-4eb8-a084-63d4020ee326

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
theorem _root_.solution (H : ℕ) :
    0 < binomialAnnulusWidth H := by
  unfold binomialAnnulusWidth
  omega
end CollatzEndpointTransport.FixedTotal
