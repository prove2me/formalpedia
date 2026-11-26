-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.orbit_loss_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:53:55.636153+00:00
-- url     : https://prove2.me/submissions/f46ce7e7-f77a-4506-9946-15d41f496b6b

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_kappa_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_kappa_mul_one_add_a0
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_kappa_lt_sixteenth

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    kappa * t + a0 * (kappa * t) + kappa * t * (kappa * t) < t / 2 := by
  have hk := kappa_pos
  have hklt := kappa_lt_sixteenth
  have hkt : 0 < kappa * t := mul_pos hk ht0
  have hlin : kappa * t + a0 * (kappa * t) = t / 16 := by
    linear_combination t * kappa_mul_one_add_a0
  have hkt16 : kappa * t < t / 16 := by nlinarith
  have hsq : kappa * t * (kappa * t) < t / 4 := by nlinarith
  linarith
end CollatzEndpointTransport.QuantitativeDensity
