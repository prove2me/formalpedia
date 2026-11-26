-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.mixedFiberRenyi_le_weighted_by_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:48:49.116896+00:00
-- url     : https://prove2.me/submissions/453412a4-c050-4cf9-ba8e-37d9ce9090e7

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_rpow_one_add_le_weighted
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_activeMixtureIndices_subset
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_local_target_renyi_sum_eq_source_sum
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inr
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inr
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
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_zero
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_basePullback
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_collatzPullback
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inr
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inr
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
attribute [local simp] CollatzEndpointTransport.OptimizedLinearPullback.psi_zero
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
    {iota : Type*} {alpha : iota → Type*} {beta : Type*}
    [∀ i, DecidableEq (alpha i)] [DecidableEq beta]
    (U : Finset iota) (W : ∀ i, Finset (alpha i))
    (f : ∀ i, alpha i → beta)
    {B theta : ℝ} (hB : 0 < B) (htheta : 0 < theta)
    (hcards : ∑ i ∈ U, ((W i).card : ℝ) ≤ B) :
    (∑ b ∈ mixedTargetSet U W f,
        (mixedFiberCard U W f b : ℝ) ^ (1 + theta)) ≤
      ∑ i ∈ activeMixtureIndices U W,
        (((W i).card : ℝ) / B) ^ (-theta) *
          ∑ x ∈ W i,
            ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by
  classical
  let V := activeMixtureIndices U W
  have hVU : V ⊆ U := activeMixtureIndices_subset U W
  have hweights :
      ∑ i ∈ V, ((W i).card : ℝ) / B ≤ 1 := by
    have hsub :
        ∑ i ∈ V, ((W i).card : ℝ) ≤
          ∑ i ∈ U, ((W i).card : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hVU
        (fun i _ _ => Nat.cast_nonneg (W i).card)
    have hVB : ∑ i ∈ V, ((W i).card : ℝ) ≤ B := hsub.trans hcards
    rw [← Finset.sum_div]
    exact (div_le_one hB).2 hVB
  have hfiber (b : beta) :
      mixedFiberCard U W f b =
        ∑ i ∈ V, (mapFiber (W i) (f i) b).card := by
    unfold mixedFiberCard
    symm
    apply Finset.sum_subset hVU
    intro i hiU hiV
    have hnot : ¬ (W i).Nonempty := by
      intro hne
      exact hiV (Finset.mem_filter.mpr ⟨hiU, hne⟩)
    have hempty : W i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    simp [mapFiber, hempty]
  calc
    (∑ b ∈ mixedTargetSet U W f,
        (mixedFiberCard U W f b : ℝ) ^ (1 + theta)) ≤
      ∑ b ∈ mixedTargetSet U W f,
        ∑ i ∈ V,
          (((W i).card : ℝ) / B) ^ (-theta) *
            ((mapFiber (W i) (f i) b).card : ℝ) ^ (1 + theta) := by
      apply Finset.sum_le_sum
      intro b hb
      rw [hfiber b, Nat.cast_sum]
      exact sum_rpow_one_add_le_weighted V
        (fun i => ((mapFiber (W i) (f i) b).card : ℝ))
        (fun i => ((W i).card : ℝ) / B)
        htheta
        (fun i hi => Nat.cast_nonneg _)
        (fun i hi => by
          have hne : (W i).Nonempty := (Finset.mem_filter.mp hi).2
          exact div_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hne)) hB)
        hweights
    _ = ∑ i ∈ V,
        (((W i).card : ℝ) / B) ^ (-theta) *
          ∑ x ∈ W i,
            ((mapFiberCardAt (W i) (f i) x : ℕ) : ℝ) ^ theta := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      congr 1
      exact local_target_renyi_sum_eq_source_sum U W f (hVU hi) htheta
end CollatzEndpointTransport.FixedTotal
