-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.admissibleExponent_tendsto_headline
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:21.33595+00:00
-- url     : https://prove2.me/submissions/321c3e0b-9859-43b1-a520-c26f261496c5

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_a0_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_log_three_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution :
    Filter.Tendsto admissibleExponent
      (nhdsWithin a0 (Set.Ioi a0)) (nhds headlineExponent) := by
  have ha0ne : a0 ≠ 0 := ne_of_gt a0_pos
  have hlog3ne : Real.log 3 ≠ 0 := ne_of_gt log_three_pos
  have hinv : ContinuousAt (fun q : ℝ => 1 / q) a0 := by
    exact continuousAt_const.div continuousAt_id ha0ne
  have hlog : ContinuousAt (fun q : ℝ => Real.log (1 / q)) a0 :=
    hinv.log (one_div_ne_zero ha0ne)
  have hcont : ContinuousAt admissibleExponent a0 := by
    change ContinuousAt (fun q : ℝ => Real.log (1 / q) / Real.log 3) a0
    exact hlog.div continuousAt_const hlog3ne
  exact hcont.tendsto.mono_left inf_le_left
end CollatzEndpointTransport.QuantitativeDensity
