-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.actualLevelBadMass_cast_le_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:36:49.674834+00:00
-- url     : https://prove2.me/submissions/e3842d46-b4ab-4eef-a4a3-14d6162f10af

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFiberSplit
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalLevelBadMass
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualLevelBadMass_eq_sum_bad
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceOddLevel
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fiber_le_ordinary_add_critical
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
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
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
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
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (S : Set ℕ) (M s : ℕ) (E : ℝ)
    (hE : 0 < E) (hs : s ≤ M) :
    (actualLevelBadMass S M s : ℝ) ≤
      E ^ 2 *
          ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (actualLevelBadEndpointSet S M s).card +
        E⁻¹ * Real.sqrt
            ((3 : ℝ) ^ (s + 1) /
              (sourceOddLevel M s).card) *
          (∑ y ∈ actualLevelEndpointSet M s,
            (actualLevelFiberCard M s y : ℝ) *
              Real.sqrt (actualLevelFiberCard M s y)) := by
  classical
  have hNnat : 0 < (sourceOddLevel M s).card := by
    rw [card_sourceOddLevel]
    exact Nat.choose_pos hs
  have hN :
      0 < ((sourceOddLevel M s).card : ℝ) := by
    exact_mod_cast hNnat
  have hR : 0 < (3 : ℝ) ^ (s + 1) := by positivity
  rw [actualLevelBadMass_eq_sum_bad]
  push_cast
  calc
    (∑ y ∈ actualLevelBadEndpointSet S M s,
        (actualLevelFiberCard M s y : ℝ)) ≤
      ∑ y ∈ actualLevelBadEndpointSet S M s,
        (E ^ 2 *
            ((sourceOddLevel M s).card : ℝ) /
            (3 : ℝ) ^ (s + 1) +
          E⁻¹ * Real.sqrt
              ((3 : ℝ) ^ (s + 1) /
                (sourceOddLevel M s).card) *
            (actualLevelFiberCard M s y : ℝ) *
              Real.sqrt (actualLevelFiberCard M s y)) := by
        apply Finset.sum_le_sum
        intro y hy
        exact fiber_le_ordinary_add_critical hE hN hR (by positivity)
    _ =
      E ^ 2 *
          ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (actualLevelBadEndpointSet S M s).card +
        E⁻¹ * Real.sqrt
            ((3 : ℝ) ^ (s + 1) /
              (sourceOddLevel M s).card) *
          (∑ y ∈ actualLevelBadEndpointSet S M s,
            (actualLevelFiberCard M s y : ℝ) *
              Real.sqrt (actualLevelFiberCard M s y)) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp only [Finset.sum_const, nsmul_eq_mul]
          ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ ≤
      E ^ 2 *
          ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (actualLevelBadEndpointSet S M s).card +
        E⁻¹ * Real.sqrt
            ((3 : ℝ) ^ (s + 1) /
              (sourceOddLevel M s).card) *
          (∑ y ∈ actualLevelEndpointSet M s,
            (actualLevelFiberCard M s y : ℝ) *
              Real.sqrt (actualLevelFiberCard M s y)) := by
        gcongr
        intro y hy
        rw [actualLevelBadEndpointSet, Finset.mem_filter] at hy
        exact hy.1
end CollatzEndpointTransport.FixedTotal
