-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedNumerator_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:22.020272+00:00
-- url     : https://prove2.me/submissions/b1eea236-7408-4292-b6d7-f1ff450fd30d

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_injective_on_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} :
    Function.Injective (fixedNumerator : FixedComposition N s → ℕ) := by
  intro c d hnum
  apply Subtype.ext
  exact
    syracuseNumerator_injective_on_length
      c.2
      d.2
      hnum
end CollatzEndpointTransport.FixedTotal
