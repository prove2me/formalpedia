-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.oddCount_le_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:24:07.691279+00:00
-- url     : https://prove2.me/submissions/32c63358-96d0-4524-b1f3-be9ed46a7235

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (H n : ℕ) : oddCount H n ≤ H := by
  unfold oddCount
  calc
    (Finset.univ.filter
      (fun i : Fin H => parityVec H n i = true)).card ≤
        (Finset.univ : Finset (Fin H)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = H := by simp
end CollatzEndpointTransport.Terras
