-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:09.951385+00:00
-- url     : https://prove2.me/submissions/473a1b91-ed5b-4fbf-afdf-e8de746e6cf8

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (k : ℕ) (ks : List ℕ) :
    0 < syracuseNumeratorList (k :: ks) := by
  simp only [syracuseNumeratorList_cons]
  positivity
end CollatzEndpointTransport.FixedTotal
