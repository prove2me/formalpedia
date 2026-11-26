-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.admissibleExponent_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:18:04.836336+00:00
-- url     : https://prove2.me/submissions/67b5098e-813f-4652-b2c6-1d2415f01553

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_log_three_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution
    {q₁ q₂ : ℝ} (hq₁0 : 0 < q₁) (hq₁q₂ : q₁ < q₂) (_hq₂1 : q₂ < 1) :
    admissibleExponent q₂ < admissibleExponent q₁ := by
  have hq₂0 : 0 < q₂ := lt_trans hq₁0 hq₁q₂
  have hinv : 1 / q₂ < 1 / q₁ :=
    one_div_lt_one_div_of_lt hq₁0 hq₁q₂
  have hlog : Real.log (1 / q₂) < Real.log (1 / q₁) :=
    Real.strictMonoOn_log
      (by exact Set.mem_Ioi.mpr (one_div_pos.mpr hq₂0))
      (by exact Set.mem_Ioi.mpr (one_div_pos.mpr hq₁0))
      hinv
  unfold admissibleExponent
  exact (div_lt_div_iff_of_pos_right log_three_pos).2 hlog
end CollatzEndpointTransport.QuantitativeDensity
