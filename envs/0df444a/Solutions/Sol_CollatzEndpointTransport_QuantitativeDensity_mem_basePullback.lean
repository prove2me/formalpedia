-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.mem_basePullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:23:17.778791+00:00
-- url     : https://prove2.me/submissions/bca628d4-413d-4ee2-a5c0-addf8483b2ae

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_TerrasInitialWindow
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution {alpha : ℝ} {S : Set ℕ} {n : ℕ} :
    n ∈ basePullback alpha S ↔ baseMap alpha n ∈ S :=
  Iff.rfl
end CollatzEndpointTransport.QuantitativeDensity
