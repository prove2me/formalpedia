-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralSourceEndpointBad_div_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:47:21.422439+00:00
-- url     : https://prove2.me/submissions/032fb978-0ef0-464d-a5b1-7466e961efce

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelBadMass_cast_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_centralSourceEndpointBad_eq_sum
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceOddLevel
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
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M : ℕ) (theta eta Q : ℝ)
    (hQ : 0 < Q) (htheta : 0 < theta) :
    ((centralSourceEndpointBad S M theta eta).card : ℝ) /
        (2 ^ M : ℝ) ≤
      C * Q * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        Q ^ (-theta) * centralEndpointInformation M theta eta := by
  classical
  rw [card_centralSourceEndpointBad_eq_sum]
  push_cast
  have hlevels :
      (∑ s ∈ Finset.range (M + 1),
          (centralLevelBadMass S M s theta eta : ℝ)) ≤
        ∑ s ∈ Finset.range (M + 1),
          (C * Q * (sourceOddLevel M s).card *
              (Real.exp (-D * Real.log 3)) ^ (s + 1) +
            Q ^ (-theta) *
              centralLevelRenyiInformation M s theta eta) := by
    apply Finset.sum_le_sum
    intro s hs
    exact centralLevelBadMass_cast_le hS M s theta eta Q hQ htheta
      (Nat.le_of_lt_succ (Finset.mem_range.mp hs))
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ M)).2
  calc
    (∑ s ∈ Finset.range (M + 1),
        (centralLevelBadMass S M s theta eta : ℝ)) ≤
      ∑ s ∈ Finset.range (M + 1),
        (C * Q * (sourceOddLevel M s).card *
            (Real.exp (-D * Real.log 3)) ^ (s + 1) +
          Q ^ (-theta) *
            centralLevelRenyiInformation M s theta eta) := hlevels
    _ = C * Q * Real.exp (-D * Real.log 3) *
          (1 + Real.exp (-D * Real.log 3)) ^ M +
        Q ^ (-theta) *
          (∑ s ∈ Finset.range (M + 1),
            centralLevelRenyiInformation M s theta eta) := by
      rw [Finset.sum_add_distrib]
      have hchoose :
          (∑ s ∈ Finset.range (M + 1),
            (M.choose s : ℝ) *
              (Real.exp (-D * Real.log 3)) ^ s) =
            (1 + Real.exp (-D * Real.log 3)) ^ M := by
        calc
          (∑ s ∈ Finset.range (M + 1),
              (M.choose s : ℝ) *
                (Real.exp (-D * Real.log 3)) ^ s) =
              (Real.exp (-D * Real.log 3) + 1) ^ M := by
            rw [add_pow]
            apply Finset.sum_congr rfl
            intro s hs
            simp [mul_assoc, mul_left_comm, mul_comm]
          _ = (1 + Real.exp (-D * Real.log 3)) ^ M := by ring
      have hord :
          (∑ s ∈ Finset.range (M + 1),
            C * Q * ((sourceOddLevel M s).card : ℝ) *
              (Real.exp (-D * Real.log 3)) ^ (s + 1)) =
            C * Q * Real.exp (-D * Real.log 3) *
              (1 + Real.exp (-D * Real.log 3)) ^ M := by
        simp_rw [card_sourceOddLevel]
        rw [show
          (∑ s ∈ Finset.range (M + 1),
            C * Q * (M.choose s : ℝ) *
              (Real.exp (-D * Real.log 3)) ^ (s + 1)) =
            C * Q * Real.exp (-D * Real.log 3) *
              (∑ s ∈ Finset.range (M + 1),
                (M.choose s : ℝ) *
                  (Real.exp (-D * Real.log 3)) ^ s) by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s hs
            ring]
        rw [hchoose]
      have hrenyi :
          (∑ s ∈ Finset.range (M + 1),
            Q ^ (-theta) *
              centralLevelRenyiInformation M s theta eta) =
            Q ^ (-theta) *
              (∑ s ∈ Finset.range (M + 1),
                centralLevelRenyiInformation M s theta eta) := by
        rw [Finset.mul_sum]
      rw [hord, hrenyi]
    _ = (C * Q * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        Q ^ (-theta) * centralEndpointInformation M theta eta) *
          (2 ^ M : ℝ) := by
      unfold centralEndpointInformation
      rw [div_pow]
      field_simp
end CollatzEndpointTransport.FixedTotal
