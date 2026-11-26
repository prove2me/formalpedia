-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.exponentCondition_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:23.471846+00:00
-- url     : https://prove2.me/submissions/75cdc49b-c3ae-4ee4-a791-c919bf3c8063

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_gammaExponent_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_admissibleExponent_mul_gamma

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution
    {a q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    a < admissibleExponent q ↔ a * gammaExponent q < 1 := by
  have hgamma : 0 < gammaExponent q := gammaExponent_pos hq0 hq1
  have hid := admissibleExponent_mul_gamma hq0 hq1
  constructor
  · intro ha
    calc
      a * gammaExponent q <
          admissibleExponent q * gammaExponent q :=
        mul_lt_mul_of_pos_right ha hgamma
      _ = 1 := hid
  · intro ha
    by_contra hnot
    have hle : admissibleExponent q ≤ a := le_of_not_gt hnot
    have hmul :
        admissibleExponent q * gammaExponent q ≤ a * gammaExponent q :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hgamma)
    rw [hid] at hmul
    linarith
end CollatzEndpointTransport.QuantitativeDensity
