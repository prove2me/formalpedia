-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.parityDigitR_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:45.748852+00:00
-- url     : https://prove2.me/submissions/93a38ea5-dae8-44ab-907f-93c0731828c7

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (n i : ℕ) : parityDigitR n i ≤ 1 := by
  cases h : parityBit ((T^[i]) n) <;> simp [parityDigitR, h]
end CollatzEndpointTransport.Terras
