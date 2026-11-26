-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.two_add_lg3_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:16:40.115573+00:00
-- url     : https://prove2.me/submissions/0137e2d6-7960-4e7c-ac45-c682e88a1703

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_lg3_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution : 0 < 2 + lg3 := by have := lg3_pos; linarith
end CollatzEndpointTransport.QuantitativeDensity
