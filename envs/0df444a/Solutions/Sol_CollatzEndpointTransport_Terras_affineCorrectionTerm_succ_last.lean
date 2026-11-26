-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.affineCorrectionTerm_succ_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:06.133552+00:00
-- url     : https://prove2.me/submissions/bf3edc14-5bf0-4f5d-9712-cc04a67c4119

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (k n : ℕ) :
    affineCorrectionTerm (k + 1) n k =
      parityDigitR n k /
        ((3 : ℝ) ^ oddCount (k + 1) n * 2) := by
  simp [affineCorrectionTerm]
end CollatzEndpointTransport.Terras
