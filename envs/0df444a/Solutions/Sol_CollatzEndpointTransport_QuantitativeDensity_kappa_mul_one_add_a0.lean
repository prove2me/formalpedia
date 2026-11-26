-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.kappa_mul_one_add_a0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:17:55.007452+00:00
-- url     : https://prove2.me/submissions/0b2cd291-f8f2-4131-a8cc-dd0d440d1080

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_two_add_lg3_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution : kappa * (1 + a0) = 1 / 16 := by
  have h : (2 : ℝ) + lg3 ≠ 0 := ne_of_gt two_add_lg3_pos
  unfold kappa a0
  field_simp
  ring
end CollatzEndpointTransport.QuantitativeDensity
