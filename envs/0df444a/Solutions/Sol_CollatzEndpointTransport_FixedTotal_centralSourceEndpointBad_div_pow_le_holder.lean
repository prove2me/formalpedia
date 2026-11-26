-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralSourceEndpointBad_div_pow_le_holder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:53:52.578808+00:00
-- url     : https://prove2.me/submissions/7b44e63b-fef1-4af9-9980-9acad0d7ce20

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiTransport
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiShellTransport
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_centralSourceEndpointBad_eq_sum
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceOddLevel
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelBadMass_div_pow_le_holder
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
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_weight_mul_rpow_mul_rpow_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_zero
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_C_pos
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
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M : ℕ) (theta eta : ℝ) (htheta : 0 < theta) :
    ((centralSourceEndpointBad S M theta eta).card : ℝ) / (2 : ℝ) ^ M ≤
      (C * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M) ^
            (theta / (1 + theta)) *
        (centralEndpointInformation M theta eta) ^
          (1 / (1 + theta)) := by
  classical
  let U := Finset.range (M + 1)
  let w : ℕ → ℝ := fun s =>
    ((sourceOddLevel M s).card : ℝ) / (2 : ℝ) ^ M
  let a : ℕ → ℝ := fun s =>
    C * (Real.exp (-D * Real.log 3)) ^ (s + 1)
  let b : ℕ → ℝ := fun s =>
    centralLevelRenyiInformation M s theta eta /
      (sourceOddLevel M s).card
  have hw : ∀ s, 0 ≤ w s := by
    intro s
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have ha : ∀ s, 0 ≤ a s := by
    intro s
    exact mul_nonneg hS.C_pos.le (by positivity)
  have hb : ∀ s, 0 ≤ b s := by
    intro s
    unfold b centralLevelRenyiInformation
    positivity
  have hlevels :
      ∑ s ∈ U,
          (centralLevelBadMass S M s theta eta : ℝ) / (2 : ℝ) ^ M ≤
        ∑ s ∈ U,
          w s * (a s) ^ (theta / (1 + theta)) *
            (b s) ^ (1 / (1 + theta)) := by
    apply Finset.sum_le_sum
    intro s hs
    exact centralLevelBadMass_div_pow_le_holder hS M s theta eta htheta
      (Nat.le_of_lt_succ (Finset.mem_range.mp hs))
  have hholder := sum_weight_mul_rpow_mul_rpow_le
    U w a b htheta hw ha hb
  have haSum :
      ∑ s ∈ U, w s * a s =
        C * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M := by
    let z := Real.exp (-D * Real.log 3)
    have hchoose :
        (∑ s ∈ Finset.range (M + 1),
          (M.choose s : ℝ) * z ^ s) = (1 + z) ^ M := by
      calc
        (∑ s ∈ Finset.range (M + 1),
            (M.choose s : ℝ) * z ^ s) = (z + 1) ^ M := by
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro s hs
          simp [mul_assoc, mul_left_comm, mul_comm]
        _ = (1 + z) ^ M := by ring
    change
      ∑ s ∈ Finset.range (M + 1),
          (((sourceOddLevel M s).card : ℝ) / (2 : ℝ) ^ M) *
            (C * z ^ (s + 1)) =
        C * z * ((1 + z) / 2) ^ M
    simp_rw [card_sourceOddLevel]
    rw [show
      (∑ s ∈ Finset.range (M + 1),
          ((M.choose s : ℝ) / (2 : ℝ) ^ M) * (C * z ^ (s + 1))) =
        (C * z / (2 : ℝ) ^ M) *
          (∑ s ∈ Finset.range (M + 1), (M.choose s : ℝ) * z ^ s) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring]
    rw [hchoose, div_pow]
    ring
  have hbSum :
      ∑ s ∈ U, w s * b s =
        centralEndpointInformation M theta eta := by
    change
      ∑ s ∈ Finset.range (M + 1),
          (((sourceOddLevel M s).card : ℝ) / (2 : ℝ) ^ M) *
            (centralLevelRenyiInformation M s theta eta /
              (sourceOddLevel M s).card) =
        centralEndpointInformation M theta eta
    have hterm : ∀ s ∈ Finset.range (M + 1),
        (((sourceOddLevel M s).card : ℝ) / (2 : ℝ) ^ M) *
            (centralLevelRenyiInformation M s theta eta /
              (sourceOddLevel M s).card) =
          centralLevelRenyiInformation M s theta eta / (2 : ℝ) ^ M := by
      intro s hs
      have hNnat : 0 < (sourceOddLevel M s).card := by
        rw [card_sourceOddLevel]
        exact Nat.choose_pos
          (Nat.le_of_lt_succ (Finset.mem_range.mp hs))
      have hN : 0 < ((sourceOddLevel M s).card : ℝ) := by
        exact_mod_cast hNnat
      field_simp [hN.ne']
    rw [show
      (∑ s ∈ Finset.range (M + 1),
          (((sourceOddLevel M s).card : ℝ) / (2 : ℝ) ^ M) *
            (centralLevelRenyiInformation M s theta eta /
              (sourceOddLevel M s).card)) =
        ∑ s ∈ Finset.range (M + 1),
          centralLevelRenyiInformation M s theta eta / (2 : ℝ) ^ M by
        apply Finset.sum_congr rfl
        exact hterm]
    rw [← Finset.sum_div]
    rfl
  rw [card_centralSourceEndpointBad_eq_sum]
  push_cast
  rw [Finset.sum_div]
  exact hlevels.trans (hholder.trans_eq (by rw [haSum, hbSum]))
end CollatzEndpointTransport.FixedTotal
