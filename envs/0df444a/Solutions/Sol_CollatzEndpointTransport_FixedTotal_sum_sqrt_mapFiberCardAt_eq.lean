-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_sqrt_mapFiberCardAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:26:23.332024+00:00
-- url     : https://prove2.me/submissions/8c4c01b7-a143-4fca-9d98-19aa22891134

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.endpointCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (W : Finset α) (f : α → β) :
    (∑ x ∈ W, Real.sqrt (mapFiberCardAt W f x)) =
      ∑ b : β,
        (mapFiber W f b).card * Real.sqrt (mapFiber W f b).card := by
  calc
    (∑ x ∈ W, Real.sqrt (mapFiberCardAt W f x)) =
        ∑ b : β, ∑ x ∈ mapFiber W f b,
          Real.sqrt (mapFiberCardAt W f x) := by
      symm
      exact Finset.sum_fiberwise W f
        (fun x => Real.sqrt (mapFiberCardAt W f x))
    _ = ∑ b : β,
        (mapFiber W f b).card * Real.sqrt (mapFiber W f b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      calc
        (∑ x ∈ mapFiber W f b,
            Real.sqrt (mapFiberCardAt W f x)) =
            ∑ _x ∈ mapFiber W f b,
              Real.sqrt (mapFiber W f b).card := by
          apply Finset.sum_congr rfl
          intro x hx
          have hfx : f x = b := (Finset.mem_filter.mp hx).2
          simp [mapFiberCardAt, hfx]
        _ = (mapFiber W f b).card *
              Real.sqrt (mapFiber W f b).card := by
          simp
end CollatzEndpointTransport.FixedTotal
