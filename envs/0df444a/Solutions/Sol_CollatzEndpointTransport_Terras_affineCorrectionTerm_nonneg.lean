-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.affineCorrectionTerm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:10:37.729812+00:00
-- url     : https://prove2.me/submissions/f5d2058e-2301-4b8c-8656-545b3a89d197

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Theorems.Thm_CollatzEndpointTransport_Terras_parityDigitR_nonneg

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (k n i : ℕ) :
    0 ≤ affineCorrectionTerm k n i := by
  unfold affineCorrectionTerm
  exact div_nonneg (parityDigitR_nonneg n i) (by positivity)
end CollatzEndpointTransport.Terras
