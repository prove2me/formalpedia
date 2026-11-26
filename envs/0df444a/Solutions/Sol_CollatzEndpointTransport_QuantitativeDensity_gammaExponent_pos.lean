-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.gammaExponent_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:17:45.73807+00:00
-- url     : https://prove2.me/submissions/4e9d3f9d-fd73-49bf-9e51-d254018cadfd

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_log_three_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_log_one_div_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < gammaExponent q := by
  exact div_pos log_three_pos (log_one_div_pos hq0 hq1)
end CollatzEndpointTransport.QuantitativeDensity
