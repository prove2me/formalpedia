-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_terminalFiber_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:42:19.2258+00:00
-- url     : https://prove2.me/submissions/09476262-1d7c-4107-9193-5a40cdfe9a5b

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPrefixMap_injective
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



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped NNReal
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.terminalCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s r : ℕ} (d : List ℕ) :
    (terminalFiber N s r d).card ≤
      (fixedSet (N - d.sum) (s - r)).card := by
  have hcard := Fintype.card_le_of_injective
    (terminalPrefixMap (N := N) (s := s) (r := r) d)
    (terminalPrefixMap_injective (N := N) (s := s) (r := r) d)
  have htarget :
      Fintype.card (FixedComposition (N - d.sum) (s - r)) =
        (fixedSet (N - d.sum) (s - r)).card := by
    exact Fintype.card_of_subtype (fixedSet (N - d.sum) (s - r))
      (by intro c; simp [fixedSet])
  rw [htarget] at hcard
  simpa [Fintype.card_coe] using hcard
end CollatzEndpointTransport.FixedTotal
