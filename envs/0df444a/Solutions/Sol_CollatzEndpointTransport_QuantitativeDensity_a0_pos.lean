-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.a0_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:16:43.75211+00:00
-- url     : https://prove2.me/submissions/d0ef4a41-9b61-4a68-9f8c-5ade4d48c70b

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_lg3_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution : 0 < a0 := by have := lg3_pos; unfold a0; linarith
end CollatzEndpointTransport.QuantitativeDensity
