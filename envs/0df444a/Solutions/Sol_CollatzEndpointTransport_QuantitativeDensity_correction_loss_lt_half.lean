-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.correction_loss_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:54:00.486483+00:00
-- url     : https://prove2.me/submissions/62128500-f3a7-4156-ac06-6f7507e701fe

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_lg3_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_two_add_lg3_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_kappa_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_kappa_lt_sixteenth

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (1 + kappa * t) * (kappa * t) + kappa * t * lg3 < t / 2 := by
  have hk := kappa_pos
  have hklt := kappa_lt_sixteenth
  have hl0 := lg3_pos
  have hp := two_add_lg3_pos
  have hkt : 0 < kappa * t := mul_pos hk ht0
  have hkt16 : kappa * t < t / 16 := by nlinarith
  -- kappa * (1 + lg3) < 1/8 because (1 + lg3)/(2 + lg3) < 1
  have hcoef : kappa * (1 + lg3) < 1 / 8 := by
    unfold kappa
    rw [div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hmain : kappa * t * (1 + lg3) < t / 8 := by nlinarith
  have hsq : kappa * t * (kappa * t) < t / 8 := by nlinarith
  nlinarith
end CollatzEndpointTransport.QuantitativeDensity
