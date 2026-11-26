-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.oddCount_eq_wordWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:07:07.450145+00:00
-- url     : https://prove2.me/submissions/44481c4d-1510-4fd1-ae48-42ce019ec1bd

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (H n : ℕ) :
    oddCount H n = wordWeight (parityVec H n) := rfl
end CollatzEndpointTransport.Terras
