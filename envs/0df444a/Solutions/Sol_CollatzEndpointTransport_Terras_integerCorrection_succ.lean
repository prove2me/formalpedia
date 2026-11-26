-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.integerCorrection_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:20:20.824728+00:00
-- url     : https://prove2.me/submissions/74bf79d6-a5b9-4ef3-97ac-e1c12f468a6f

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (k n : ℕ) :
    integerCorrection (k + 1) n =
      if parityBit ((T^[k]) n) then
        3 * integerCorrection k n + 2 ^ k
      else
        integerCorrection k n := rfl
end CollatzEndpointTransport.Terras
