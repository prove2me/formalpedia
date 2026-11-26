-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.centralOrbitScale_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:18:38.399589+00:00
-- url     : https://prove2.me/submissions/4b1e7e5b-9ebd-40ab-b34e-6a316ecc105b

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasOrbitEnvelope

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
open scoped Real
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (k : ℕ) :
    0 < centralOrbitScale k := by
  unfold centralOrbitScale
  positivity
end CollatzEndpointTransport.Terras
