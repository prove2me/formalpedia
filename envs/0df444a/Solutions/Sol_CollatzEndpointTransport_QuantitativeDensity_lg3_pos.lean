-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.lg3_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:35.886848+00:00
-- url     : https://prove2.me/submissions/068a168c-08a3-4ad0-ad2c-1b7eb64038f9

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution : 0 < lg3 := Real.logb_pos (by norm_num) (by norm_num)
end CollatzEndpointTransport.QuantitativeDensity
