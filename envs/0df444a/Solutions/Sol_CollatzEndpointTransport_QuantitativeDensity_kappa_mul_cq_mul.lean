-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.kappa_mul_cq_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:38:22.422818+00:00
-- url     : https://prove2.me/submissions/1b73dbf7-9251-4e64-8cd3-3e3464f5aabc

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_kappa_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution (q : ℝ) (hq : 0 < q) :
    kappa * cq q * q = (q - a0) / 4 := by
  have hk : kappa ≠ 0 := ne_of_gt kappa_pos
  have hq' : q ≠ 0 := ne_of_gt hq
  unfold cq
  field_simp
end CollatzEndpointTransport.QuantitativeDensity
