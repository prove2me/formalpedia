-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.admissibleExponent_mul_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:19:04.084353+00:00
-- url     : https://prove2.me/submissions/610857f2-0399-412e-8c7e-879b00404e3e

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_log_three_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_log_one_div_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    admissibleExponent q * gammaExponent q = 1 := by
  have hlogne : Real.log (1 / q) ≠ 0 :=
    ne_of_gt (log_one_div_pos hq0 hq1)
  have hlog3ne : Real.log 3 ≠ 0 := ne_of_gt log_three_pos
  unfold admissibleExponent gammaExponent
  field_simp
end CollatzEndpointTransport.QuantitativeDensity
