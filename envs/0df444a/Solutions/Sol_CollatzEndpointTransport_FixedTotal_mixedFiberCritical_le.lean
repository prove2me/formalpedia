-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.mixedFiberCritical_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:30:21.103738+00:00
-- url     : https://prove2.me/submissions/aef426ed-9c2f-451b-b32c-336f4f2a2dca

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_mul_sqrt_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_local_target_sum_eq_source_sum
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
    (f : ∀ i, α i → β) :
    (∑ b ∈ mixedTargetSet U W f,
        (mixedFiberCard U W f b : ℝ) *
          Real.sqrt (mixedFiberCard U W f b)) ≤
      Real.sqrt U.card *
        ∑ i ∈ U, ∑ x ∈ W i,
          Real.sqrt (mapFiberCardAt (W i) (f i) x) := by
  calc
    (∑ b ∈ mixedTargetSet U W f,
        (mixedFiberCard U W f b : ℝ) *
          Real.sqrt (mixedFiberCard U W f b)) ≤
      ∑ b ∈ mixedTargetSet U W f,
        Real.sqrt U.card *
          ∑ i ∈ U,
            ((mapFiber (W i) (f i) b).card : ℝ) *
              Real.sqrt (mapFiber (W i) (f i) b).card := by
      apply Finset.sum_le_sum
      intro b hb
      simpa [mixedFiberCard] using
        sum_mul_sqrt_le U
          (fun i => (mapFiber (W i) (f i) b).card)
    _ = Real.sqrt U.card *
        ∑ i ∈ U, ∑ x ∈ W i,
          Real.sqrt (mapFiberCardAt (W i) (f i) x) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      apply congrArg (fun z : ℝ => Real.sqrt U.card * z)
      apply Finset.sum_congr rfl
      intro i hi
      exact local_target_sum_eq_source_sum U W f hi
end CollatzEndpointTransport.FixedTotal
