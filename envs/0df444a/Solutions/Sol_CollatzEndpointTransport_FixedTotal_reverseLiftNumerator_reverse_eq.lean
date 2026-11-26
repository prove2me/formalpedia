-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_reverse_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:43:07.182493+00:00
-- url     : https://prove2.me/submissions/07ca8380-a552-4f45-ab58-982d9631555c

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_append_singleton_central
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne


attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (ks : List ℕ) :
    reverseLiftNumerator ks.reverse =
      3 ^ ks.length + syracuseNumeratorList ks := by
  induction ks using List.reverseRecOn with
  | nil => simp
  | append_singleton ks k ih =>
      rw [List.reverse_append, List.reverse_singleton,
        List.singleton_append, reverseLiftNumerator_cons, ih,
        syracuseNumeratorList_append_singleton_central]
      simp only [List.length_append, List.length_singleton,
        List.sum_reverse]
      rw [pow_succ]
      ring
end CollatzEndpointTransport.FixedTotal
