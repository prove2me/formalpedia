-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.headlineExponent_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:20.358834+00:00
-- url     : https://prove2.me/submissions/bdf9be76-fe56-4f5d-a2a5-209bc455b310

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_lg3_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution :
    headlineExponent = Real.log (2 / lg3) / Real.log 3 := by
  have hlg3 : lg3 ≠ 0 := ne_of_gt lg3_pos
  have harg : 1 / a0 = 2 / lg3 := by
    unfold a0
    field_simp
  simp only [headlineExponent, admissibleExponent, harg]
end CollatzEndpointTransport.QuantitativeDensity
