-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralLevelBadMass_cast_le_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:39.742729+00:00
-- url     : https://prove2.me/submissions/8e2a2d2e-b76f-43aa-baba-97bcbd828e6e

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelBadMass_eq_sum_bad
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceOddLevel
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fiber_le_ordinary_add_renyi
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
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (S : Set ℕ) (M s : ℕ) (theta eta Q : ℝ)
    (hQ : 0 < Q) (htheta : 0 < theta) (hs : s ≤ M) :
    (centralLevelBadMass S M s theta eta : ℝ) ≤
      Q * ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (centralLevelBadEndpointSet S M s theta eta).card +
        Q ^ (-theta) *
          (((3 : ℝ) ^ (s + 1)) /
            (sourceOddLevel M s).card) ^ theta *
          (∑ y ∈ centralLevelEndpointSet M s theta eta,
            (centralLevelFiberCard M s theta eta y : ℝ) ^
              (1 + theta)) := by
  classical
  have hNnat : 0 < (sourceOddLevel M s).card := by
    rw [card_sourceOddLevel]
    exact Nat.choose_pos hs
  have hN : 0 < ((sourceOddLevel M s).card : ℝ) := by
    exact_mod_cast hNnat
  have hR : 0 < (3 : ℝ) ^ (s + 1) := by positivity
  rw [centralLevelBadMass_eq_sum_bad]
  push_cast
  calc
    (∑ y ∈ centralLevelBadEndpointSet S M s theta eta,
        (centralLevelFiberCard M s theta eta y : ℝ)) ≤
      ∑ y ∈ centralLevelBadEndpointSet S M s theta eta,
        (Q * ((sourceOddLevel M s).card : ℝ) /
            (3 : ℝ) ^ (s + 1) +
          Q ^ (-theta) *
            (((3 : ℝ) ^ (s + 1)) /
              (sourceOddLevel M s).card) ^ theta *
            (centralLevelFiberCard M s theta eta y : ℝ) ^
              (1 + theta)) := by
        apply Finset.sum_le_sum
        intro y hy
        exact fiber_le_ordinary_add_renyi hQ hN hR (by positivity) htheta
    _ = Q * ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (centralLevelBadEndpointSet S M s theta eta).card +
        Q ^ (-theta) *
          (((3 : ℝ) ^ (s + 1)) /
            (sourceOddLevel M s).card) ^ theta *
          (∑ y ∈ centralLevelBadEndpointSet S M s theta eta,
            (centralLevelFiberCard M s theta eta y : ℝ) ^
              (1 + theta)) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp only [Finset.sum_const, nsmul_eq_mul]
          ring
        · rw [Finset.mul_sum]
    _ ≤ Q * ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (centralLevelBadEndpointSet S M s theta eta).card +
        Q ^ (-theta) *
          (((3 : ℝ) ^ (s + 1)) /
            (sourceOddLevel M s).card) ^ theta *
          (∑ y ∈ centralLevelEndpointSet M s theta eta,
            (centralLevelFiberCard M s theta eta y : ℝ) ^
              (1 + theta)) := by
        gcongr
        intro y hy
        exact (Finset.mem_filter.mp hy).1
end CollatzEndpointTransport.FixedTotal
