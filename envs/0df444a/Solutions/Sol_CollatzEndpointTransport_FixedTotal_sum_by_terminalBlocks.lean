-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_by_terminalBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:53.517362+00:00
-- url     : https://prove2.me/submissions/c681d92c-40a2-4795-be9a-0ab6f691166d

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
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
    {R : Type*} [CommSemiring R]
    {N s r : ℕ} (f : List ℕ → R) :
    (∑ c ∈ fixedSet N s, f (terminalBlocks c r)) =
      ∑ d ∈ terminalPatternImage N s r,
        (terminalFiber N s r d).card * f d := by
  calc
    (∑ c ∈ fixedSet N s, f (terminalBlocks c r)) =
        ∑ d ∈ terminalPatternImage N s r,
          ∑ c ∈ terminalFiber N s r d,
            f (terminalBlocks c r) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun c hc => Finset.mem_image.mpr ⟨c, hc, rfl⟩)
        (fun c => f (terminalBlocks c r))
    _ = ∑ d ∈ terminalPatternImage N s r,
        (terminalFiber N s r d).card * f d := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        (∑ c ∈ terminalFiber N s r d,
            f (terminalBlocks c r)) =
            ∑ _c ∈ terminalFiber N s r d, f d := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [(mem_terminalFiber_iff.mp hc).2]
        _ = (terminalFiber N s r d).card * f d := by simp
end CollatzEndpointTransport.FixedTotal
