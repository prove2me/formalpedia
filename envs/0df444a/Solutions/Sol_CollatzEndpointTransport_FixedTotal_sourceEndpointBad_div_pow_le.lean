-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:42.785266+00:00
-- url     : https://prove2.me/submissions/6ad46436-2c36-47ed-8342-93cb27a0d592

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalLevelBadMass
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualLevelBadMass_cast_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceEndpointBad_eq_sum_levelBadMass
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceOddLevel
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
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_zero
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
attribute [local simp] CollatzEndpointTransport.OptimizedLinearPullback.psi_zero
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
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M : ℕ) (hM : 1 ≤ M) (E : ℝ) (hE : 0 < E) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      C * E ^ 2 * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        E⁻¹ * actualCriticalEndpointInformation M := by
  classical
  rw [card_sourceEndpointBad_eq_sum_levelBadMass]
  push_cast
  have hlevels :
      (∑ s ∈ Finset.range (M + 1),
          (actualLevelBadMass S M s : ℝ)) ≤
        ∑ s ∈ Finset.range (M + 1),
          (C * E ^ 2 * (sourceOddLevel M s).card *
              (Real.exp (-D * Real.log 3)) ^ (s + 1) +
            E⁻¹ * Real.sqrt 3 *
              actualLevelCriticalContribution M s) := by
    apply Finset.sum_le_sum
    intro s hs
    exact actualLevelBadMass_cast_le hS M s E hE
      (Nat.le_of_lt_succ (Finset.mem_range.mp hs))
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ M)).2
  calc
    (∑ s ∈ Finset.range (M + 1),
        (actualLevelBadMass S M s : ℝ)) ≤
      ∑ s ∈ Finset.range (M + 1),
        (C * E ^ 2 * (sourceOddLevel M s).card *
            (Real.exp (-D * Real.log 3)) ^ (s + 1) +
          E⁻¹ * Real.sqrt 3 *
            actualLevelCriticalContribution M s) := hlevels
    _ =
      C * E ^ 2 * Real.exp (-D * Real.log 3) *
          (1 + Real.exp (-D * Real.log 3)) ^ M +
        E⁻¹ * Real.sqrt 3 *
          (∑ s ∈ Finset.range (M + 1),
            actualLevelCriticalContribution M s) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · have hchoose :
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
          simp_rw [card_sourceOddLevel]
          rw [show
            (∑ s ∈ Finset.range (M + 1),
              C * E ^ 2 * (M.choose s : ℝ) *
                (Real.exp (-D * Real.log 3)) ^ (s + 1)) =
              C * E ^ 2 * Real.exp (-D * Real.log 3) *
                (∑ s ∈ Finset.range (M + 1),
                  (M.choose s : ℝ) *
                    (Real.exp (-D * Real.log 3)) ^ s) by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s hs
              ring]
          rw [hchoose]
        · rw [Finset.mul_sum]
    _ =
      (C * E ^ 2 * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        E⁻¹ * actualCriticalEndpointInformation M) *
          (2 ^ M : ℝ) := by
        unfold actualCriticalEndpointInformation
        rw [div_pow]
        field_simp
end CollatzEndpointTransport.FixedTotal
