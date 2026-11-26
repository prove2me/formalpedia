-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:20:35.042106+00:00
-- url     : https://prove2.me/submissions/6bc2d139-dabd-49d9-a9d0-70d30ad2113f

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (k : ℕ) (ks : List ℕ) :
    syracuseNumeratorList (k :: ks) =
      3 ^ ks.length + 2 ^ k * syracuseNumeratorList ks := rfl
end CollatzEndpointTransport.FixedTotal
