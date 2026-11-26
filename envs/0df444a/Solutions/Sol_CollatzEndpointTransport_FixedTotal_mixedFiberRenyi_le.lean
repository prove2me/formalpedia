-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.mixedFiberRenyi_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:31:18.120487+00:00
-- url     : https://prove2.me/submissions/49f1a372-c161-41f0-bd07-677877260968

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_rpow_one_add_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_local_target_renyi_sum_eq_source_sum
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_basePullback
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_collatzPullback
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.normalizedReverseLift_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_basePullback
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {ι : Type*} {α : ι → Type*} {β : Type*}
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (U : Finset ι) (W : ∀ i, Finset (α i))
    (f : ∀ i, α i → β)
    {theta : ℝ} (htheta : 0 < theta) :
    (∑ b ∈ mixedTargetSet U W f,
        (mixedFiberCard U W f b : ℝ) ^ (1 + theta)) ≤
      (U.card : ℝ) ^ theta *
        ∑ i ∈ U, ∑ x ∈ W i,
          ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by
  calc
    (∑ b ∈ mixedTargetSet U W f,
        (mixedFiberCard U W f b : ℝ) ^ (1 + theta)) ≤
      ∑ b ∈ mixedTargetSet U W f,
        (U.card : ℝ) ^ theta *
          ∑ i ∈ U,
            ((mapFiber (W i) (f i) b).card : ℝ) ^ (1 + theta) := by
      apply Finset.sum_le_sum
      intro b hb
      simpa [mixedFiberCard] using
        sum_rpow_one_add_le U
          (fun i => (mapFiber (W i) (f i) b).card) htheta
    _ = (U.card : ℝ) ^ theta *
        ∑ i ∈ U, ∑ x ∈ W i,
          ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      apply congrArg (fun z : ℝ => (U.card : ℝ) ^ theta * z)
      apply Finset.sum_congr rfl
      intro i hi
      exact local_target_renyi_sum_eq_source_sum U W f hi htheta
end CollatzEndpointTransport.FixedTotal
