-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.integerCorrection_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:20:01.745826+00:00
-- url     : https://prove2.me/submissions/a6d5d6ae-52c0-4971-bda1-4a0fa1ec3e46

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (n : ℕ) :
    integerCorrection 0 n = 0 := rfl
end CollatzEndpointTransport.Terras
