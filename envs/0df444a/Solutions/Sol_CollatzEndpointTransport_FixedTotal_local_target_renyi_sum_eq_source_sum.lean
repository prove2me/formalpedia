-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.local_target_renyi_sum_eq_source_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:04:20.243588+00:00
-- url     : https://prove2.me/submissions/b8785977-6e29-4441-bb18-e7425b0026e7

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_map_mem_mixedTargetSet
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
    {i : ι} (hi : i ∈ U) {theta : ℝ} (htheta : 0 < theta) :
    (∑ b ∈ mixedTargetSet U W f,
        ((mapFiber (W i) (f i) b).card : ℝ) ^ (1 + theta)) =
      ∑ x ∈ W i,
        ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by
  have hmaps :
      ∀ x ∈ W i, f i x ∈ mixedTargetSet U W f :=
    fun x hx => map_mem_mixedTargetSet U W f hi hx
  calc
    (∑ b ∈ mixedTargetSet U W f,
        ((mapFiber (W i) (f i) b).card : ℝ) ^ (1 + theta)) =
      ∑ b ∈ mixedTargetSet U W f,
        ∑ x ∈ mapFiber (W i) (f i) b,
          ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hzero : (mapFiber (W i) (f i) b).card = 0
      · have hempty := Finset.card_eq_zero.mp hzero
        have hexponent : 1 + theta ≠ 0 := by linarith
        simp [hempty, hzero, Real.zero_rpow hexponent]
      · have hcardR : 0 < ((mapFiber (W i) (f i) b).card : ℝ) :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero)
        calc
          ((mapFiber (W i) (f i) b).card : ℝ) ^ (1 + theta) =
              ((mapFiber (W i) (f i) b).card : ℝ) *
                ((mapFiber (W i) (f i) b).card : ℝ) ^ theta := by
            rw [Real.rpow_add hcardR]
            simp
          _ = ∑ x ∈ mapFiber (W i) (f i) b,
              ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by
            calc
              ((mapFiber (W i) (f i) b).card : ℝ) *
                    ((mapFiber (W i) (f i) b).card : ℝ) ^ theta =
                  ∑ _x ∈ mapFiber (W i) (f i) b,
                    ((mapFiber (W i) (f i) b).card : ℝ) ^ theta := by simp
              _ = _ := by
                apply Finset.sum_congr rfl
                intro x hx
                have hfx : f i x = b := (Finset.mem_filter.mp hx).2
                simp [mapFiberCardAt, hfx]
    _ = ∑ x ∈ W i,
        ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by
      exact Finset.sum_fiberwise_of_maps_to hmaps
        (fun x => ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta)
end CollatzEndpointTransport.FixedTotal
