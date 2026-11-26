-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.affineCorrectionTerm_succ_old
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:27.10705+00:00
-- url     : https://prove2.me/submissions/fb610073-03c6-4f04-93c8-cdfd9d43b05a

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {k n i : ℕ} (hi : i < k) :
    affineCorrectionTerm (k + 1) n i =
      affineCorrectionTerm k n i / 2 := by
  have hsub : k + 1 - i = (k - i) + 1 := by omega
  unfold affineCorrectionTerm
  rw [hsub, pow_succ]
  ring
end CollatzEndpointTransport.Terras
