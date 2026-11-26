-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.kappa_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:17:50.070147+00:00
-- url     : https://prove2.me/submissions/b4cae9e8-b489-4ab8-8df0-51017edcdd8b

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_two_add_lg3_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution : 0 < kappa := by
  have h := two_add_lg3_pos
  unfold kappa
  exact div_pos one_pos (by linarith)
end CollatzEndpointTransport.QuantitativeDensity
