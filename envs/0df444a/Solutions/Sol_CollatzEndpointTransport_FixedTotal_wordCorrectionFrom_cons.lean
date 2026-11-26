-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:27:11.110817+00:00
-- url     : https://prove2.me/submissions/e777cd01-6d90-432c-9b68-afd7fcaffcc9

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (i c : ℕ) (b : Bool) (bs : List Bool) :
    wordCorrectionFrom i c (b :: bs) =
      wordCorrectionFrom (i + 1)
        (if b then 3 * c + 2 ^ i else c) bs := rfl
end CollatzEndpointTransport.FixedTotal
