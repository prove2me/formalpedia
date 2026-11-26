-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.admissibleExponent_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:54:47.8068+00:00
-- url     : https://prove2.me/submissions/b39be248-cf51-4c58-96a1-81ac5960e518

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_log_three_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_log_one_div_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < admissibleExponent q := by
  exact div_pos (log_one_div_pos hq0 hq1) log_three_pos
end CollatzEndpointTransport.QuantitativeDensity
