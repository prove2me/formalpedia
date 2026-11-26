-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.cap_clears_requirement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:54:36.373953+00:00
-- url     : https://prove2.me/submissions/8d58e88c-38ee-4fcd-9c00-a8190b26968f

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution
    {lam q : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hqa : a0 < q) :
    lam * (q - a0) / 4 < lam * (q - a0) / (2 * (1 - lam)) := by
  have hnum : 0 < lam * (q - a0) := mul_pos hlam0 (by linarith)
  have hden : 0 < 2 * (1 - lam) := by linarith
  rw [div_lt_div_iff₀ (by norm_num) hden]
  nlinarith
end CollatzEndpointTransport.QuantitativeDensity
