-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.kappa_lt_sixteenth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:17:50.690183+00:00
-- url     : https://prove2.me/submissions/9bd2fdad-9cf9-48f3-9ab0-ae035d3a94c4

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_lg3_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_two_add_lg3_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution : kappa < 1 / 16 := by
  have h := lg3_pos
  have hp := two_add_lg3_pos
  unfold kappa
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith
end CollatzEndpointTransport.QuantitativeDensity
