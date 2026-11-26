-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.bConst_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:53:07.164532+00:00
-- url     : https://prove2.me/submissions/7ea54ccb-49b9-4812-87e7-0ef6a00e2ad2

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_a0_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution : bConst < 1 := by have := a0_pos; unfold bConst; linarith
end CollatzEndpointTransport.QuantitativeDensity
