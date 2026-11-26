-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.cq_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:54:19.831794+00:00
-- url     : https://prove2.me/submissions/e841b311-bcb9-4ed0-a38c-307ad2a09f89

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_kappa_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution {q : ℝ} (hq : 0 < q) (hqa : a0 < q) : 0 < cq q := by
  have hk := kappa_pos
  unfold cq
  exact div_pos (by linarith) (by nlinarith)
end CollatzEndpointTransport.QuantitativeDensity
