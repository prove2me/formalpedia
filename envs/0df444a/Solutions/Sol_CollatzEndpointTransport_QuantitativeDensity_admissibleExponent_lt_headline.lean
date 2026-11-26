-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.admissibleExponent_lt_headline
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:17.726721+00:00
-- url     : https://prove2.me/submissions/92bd2606-91b5-4cad-8a3b-21ebeb6a65f7

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_a0_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_admissibleExponent_strictAnti

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution
    {q : ℝ} (hqa : a0 < q) (hq1 : q < 1) :
    admissibleExponent q < headlineExponent := by
  unfold headlineExponent
  exact admissibleExponent_strictAnti a0_pos hqa hq1
end CollatzEndpointTransport.QuantitativeDensity
