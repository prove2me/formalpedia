-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.lg3_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:37.046855+00:00
-- url     : https://prove2.me/submissions/05cea3dd-f880-4fef-9e8a-4fbe6df00b80

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution : 1 < QuantitativeDensity.lg3 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 < Real.log 3 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  unfold QuantitativeDensity.lg3 Real.logb
  exact (lt_div_iff₀ hlog2).2 (by simpa [one_mul] using hlog)
end CollatzEndpointTransport.Terras
