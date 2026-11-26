-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.parityVec_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:46:13.53365+00:00
-- url     : https://prove2.me/submissions/4c0f8e12-a6dc-439c-8314-af86e646dc7c

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M n : ℕ) :
    (fun i : Fin M => Terras.parityVec (M + 1) n i.castSucc) =
      Terras.parityVec M n := by
  rfl
end CollatzEndpointTransport.FixedTotal
