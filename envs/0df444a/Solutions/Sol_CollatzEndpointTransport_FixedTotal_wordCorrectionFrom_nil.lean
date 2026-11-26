-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:26:47.180194+00:00
-- url     : https://prove2.me/submissions/72ce193e-740b-4fe3-9b98-b3be53852b4b

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (i c : ℕ) :
    wordCorrectionFrom i c [] = c := rfl
end CollatzEndpointTransport.FixedTotal
