-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.local_target_sum_eq_source_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:26:28.894332+00:00
-- url     : https://prove2.me/submissions/bc73c837-0415-4477-b262-b0f6736bc6e4

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_map_mem_mixedTargetSet
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
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β)
    {i : ι} (hi : i ∈ U) :
    (∑ b ∈ mixedTargetSet U W f,
        (mapFiber (W i) (f i) b).card *
          Real.sqrt (mapFiber (W i) (f i) b).card) =
      ∑ x ∈ W i, Real.sqrt (mapFiberCardAt (W i) (f i) x) := by
  have hmaps :
      ∀ x ∈ W i, f i x ∈ mixedTargetSet U W f :=
    fun x hx => map_mem_mixedTargetSet U W f hi hx
  calc
    (∑ b ∈ mixedTargetSet U W f,
        (mapFiber (W i) (f i) b).card *
          Real.sqrt (mapFiber (W i) (f i) b).card) =
      ∑ b ∈ mixedTargetSet U W f,
        ∑ x ∈ mapFiber (W i) (f i) b,
          Real.sqrt (mapFiberCardAt (W i) (f i) x) := by
      apply Finset.sum_congr rfl
      intro b hb
      symm
      calc
        (∑ x ∈ mapFiber (W i) (f i) b,
            Real.sqrt (mapFiberCardAt (W i) (f i) x)) =
            ∑ _x ∈ mapFiber (W i) (f i) b,
              Real.sqrt (mapFiber (W i) (f i) b).card := by
          apply Finset.sum_congr rfl
          intro x hx
          have hfx : f i x = b := (Finset.mem_filter.mp hx).2
          simp [mapFiberCardAt, hfx]
        _ = (mapFiber (W i) (f i) b).card *
              Real.sqrt (mapFiber (W i) (f i) b).card := by
          simp
    _ = ∑ x ∈ W i,
        Real.sqrt (mapFiberCardAt (W i) (f i) x) := by
      exact Finset.sum_fiberwise_of_maps_to hmaps
        (fun x => Real.sqrt (mapFiberCardAt (W i) (f i) x))
end CollatzEndpointTransport.FixedTotal
