-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.syracuseNumerator_injective_on_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:35.139016+00:00
-- url     : https://prove2.me/submissions/5c8dc6e1-aa3c-4521-b2b8-92552d18d8bb

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_injective_of_length_sum
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} {c d : Composition N}
    (hc : c.length = s) (hd : d.length = s)
    (hnum : syracuseNumerator c = syracuseNumerator d) :
    c = d := by
  apply Composition.ext
  apply syracuseNumeratorList_injective_of_length_sum s
  · exact hc
  · exact hd
  · intro k hk
    exact c.blocks_pos hk
  · intro k hk
    exact d.blocks_pos hk
  · rw [c.blocks_sum, d.blocks_sum]
  · exact hnum
end CollatzEndpointTransport.FixedTotal
