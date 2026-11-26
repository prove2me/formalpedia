-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralLevelBadMass_cast_le_holder_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:49:22.052242+00:00
-- url     : https://prove2.me/submissions/8f8f15d9-9f81-4d7c-8622-17897f7b7156

import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiTransport
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelBadMass_eq_sum_bad
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
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
    (S : Set ℕ) (M s : ℕ) (theta eta : ℝ)
    (htheta : 0 < theta) :
    (centralLevelBadMass S M s theta eta : ℝ) ≤
      ((centralLevelBadEndpointSet S M s theta eta).card : ℝ) ^
          (theta / (1 + theta)) *
        (∑ y ∈ centralLevelEndpointSet M s theta eta,
          (centralLevelFiberCard M s theta eta y : ℝ) ^ (1 + theta)) ^
            (1 / (1 + theta)) := by
  classical
  let E := centralLevelBadEndpointSet S M s theta eta
  let V := centralLevelEndpointSet M s theta eta
  let p := (1 + theta) / theta
  let q := 1 + theta
  have hq : 0 < q := by dsimp [q]; linarith
  have hp : 1 < p := by
    dsimp [p]
    rw [lt_div_iff₀ htheta]
    linarith
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp, ?_⟩
    dsimp [p, q]
    field_simp [htheta.ne', hq.ne']
    ring
  have hholder := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := E) (f := fun _y => (1 : ℝ))
    (g := fun y => (centralLevelFiberCard M s theta eta y : ℝ))
    hpq (by intro i hi; positivity) (by intro i hi; positivity)
  have hsumFiber :
      (∑ y ∈ E, (1 : ℝ) *
          (centralLevelFiberCard M s theta eta y : ℝ)) =
        (centralLevelBadMass S M s theta eta : ℝ) := by
    rw [centralLevelBadMass_eq_sum_bad]
    push_cast
    simp [E]
  have hones : ∑ _y ∈ E, (1 : ℝ) ^ p = (E.card : ℝ) := by simp
  have hmomentSubset :
      (∑ y ∈ E,
          (centralLevelFiberCard M s theta eta y : ℝ) ^ q) ≤
        ∑ y ∈ V,
          (centralLevelFiberCard M s theta eta y : ℝ) ^ q := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro y hy
      exact (Finset.mem_filter.mp hy).1
    · intro y hyV hyE
      positivity
  have hrootMono :
      (∑ y ∈ E,
          (centralLevelFiberCard M s theta eta y : ℝ) ^ q) ^ (1 / q) ≤
        (∑ y ∈ V,
          (centralLevelFiberCard M s theta eta y : ℝ) ^ q) ^ (1 / q) := by
    exact Real.rpow_le_rpow (sum_nonneg fun _ _ => by positivity)
      hmomentSubset (by positivity)
  have hexp : 1 / p = theta / (1 + theta) := by
    dsimp [p]
    field_simp [htheta.ne', hq.ne']
  rw [hsumFiber, hones, hexp] at hholder
  calc
    (centralLevelBadMass S M s theta eta : ℝ) ≤
        (E.card : ℝ) ^ (theta / (1 + theta)) *
          (∑ y ∈ E,
            (centralLevelFiberCard M s theta eta y : ℝ) ^ q) ^
              (1 / q) := hholder
    _ ≤ (E.card : ℝ) ^ (theta / (1 + theta)) *
          (∑ y ∈ V,
            (centralLevelFiberCard M s theta eta y : ℝ) ^ q) ^
              (1 / q) :=
      mul_le_mul_of_nonneg_left hrootMono
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := by simp [E, V, q]
end CollatzEndpointTransport.FixedTotal
