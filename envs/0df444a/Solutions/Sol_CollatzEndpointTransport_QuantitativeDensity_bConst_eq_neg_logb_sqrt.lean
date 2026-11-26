-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.bConst_eq_neg_logb_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:53:49.558677+00:00
-- url     : https://prove2.me/submissions/0a788c39-b087-4b26-8683-99e98de8c342

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution :
    bConst = -Real.logb 2 (Real.sqrt 3 / 2) := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hlog : Real.log (Real.sqrt 3) = Real.log 3 / 2 :=
    Real.log_sqrt (by norm_num)
  have hl2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold bConst a0 lg3
  simp only [Real.logb]
  rw [Real.log_div hs (by norm_num), hlog]
  field_simp
  ring
end CollatzEndpointTransport.QuantitativeDensity
