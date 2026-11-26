-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.parityDigitR_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:39.384702+00:00
-- url     : https://prove2.me/submissions/72b49951-ad91-4bbf-9ee8-5a9160ed68d5

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (n i : ℕ) : 0 ≤ parityDigitR n i := by
  cases h : parityBit ((T^[i]) n) <;> simp [parityDigitR, h]
end CollatzEndpointTransport.Terras
