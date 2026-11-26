-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.log_one_div_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:36.59625+00:00
-- url     : https://prove2.me/submissions/880a00a2-966c-42e4-bfd5-660ad6c19337

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < Real.log (1 / q) := by
  apply Real.log_pos
  rw [one_div]
  exact (one_lt_inv₀ hq0).2 hq1
end CollatzEndpointTransport.QuantitativeDensity
