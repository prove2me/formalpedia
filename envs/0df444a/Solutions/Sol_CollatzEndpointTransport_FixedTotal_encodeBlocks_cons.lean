-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:27:00.02428+00:00
-- url     : https://prove2.me/submissions/90c0f42c-8850-449f-9c41-d32748b29b12

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (k : ℕ) (ks : List ℕ) :
    encodeBlocks (k :: ks) = encodePart k ++ encodeBlocks ks := rfl
end CollatzEndpointTransport.FixedTotal
