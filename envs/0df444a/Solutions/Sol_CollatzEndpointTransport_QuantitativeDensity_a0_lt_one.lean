-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.a0_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:17:10.216003+00:00
-- url     : https://prove2.me/submissions/0d202bc3-cea9-40e8-8fb1-c7450d3a9a3f

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_lg3_lt_two

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution : a0 < 1 := by have := lg3_lt_two; unfold a0; linarith
end CollatzEndpointTransport.QuantitativeDensity
