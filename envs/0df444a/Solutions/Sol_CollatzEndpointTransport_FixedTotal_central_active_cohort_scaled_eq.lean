-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.central_active_cohort_scaled_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:47:48.188384+00:00
-- url     : https://prove2.me/submissions/edfdaa2c-9775-46aa-a9ae-b4b91ed3727e

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceOddLevel
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelCohortSet_eq_fixed
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortRenyiSourceMoment_eq_fixed
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
    {M s : ℕ} {theta eta : ℝ} (u : Fin M)
    (hadm : CentralRenyiAdmissible (M - (u : ℕ)) s theta eta) :
    ((((3 : ℝ) ^ (s + 1)) ^ theta /
        (((sourceOddLevel M s).card : ℝ) ^ theta)) *
      (((centralLevelCohortSet M s theta eta u).card : ℝ) /
          ((sourceOddLevel M s).card : ℝ)) ^ (-theta) *
      (∑ c ∈ centralLevelCohortSet M s theta eta u,
        ((mapFiberCardAt
          (centralLevelCohortSet M s theta eta u)
          (cohortEndpoint u) c : ℕ) : ℝ) ^ theta)) =
      (3 : ℝ) ^ theta *
        (((fixedSet (M - (u : ℕ)) s).card : ℝ) *
          fixedRenyiMoment (M - (u : ℕ)) s theta) := by
  rw [centralLevelCohortSet_eq_fixed u hadm]
  let N := M - (u : ℕ)
  let L : ℝ := (fixedSet N s).card
  let B : ℝ := (sourceOddLevel M s).card
  have hs : 0 < s := Nat.zero_lt_one.trans hadm.2.1
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.zero_lt_one.trans hadm.1
  have hL : 0 < L := by
    dsimp [L]
    rw [card_fixedSet N s hN hs]
    exact_mod_cast Nat.choose_pos
      (Nat.sub_le_sub_right (Nat.le_of_lt hadm.2.2.1) 1)
  have hB : 0 < B := by
    dsimp [B]
    rw [card_sourceOddLevel]
    have hsM : s ≤ M :=
      (Nat.le_of_lt hadm.2.2.1).trans (Nat.sub_le M (u : ℕ))
    exact_mod_cast Nat.choose_pos hsM
  have hbridge := cohortRenyiSourceMoment_eq_fixed M u s theta
  have hlocal :
      (((3 : ℝ) ^ s) ^ theta) *
          (∑ c ∈ fixedSet N s,
            ((mapFiberCardAt (fixedSet N s) (cohortEndpoint u) c : ℕ) : ℝ) ^ theta) =
        fixedRenyiNumerator N s theta := by
    simpa [cohortRenyiSourceMoment, N] using hbridge
  have hmoment :
      L * fixedRenyiMoment N s theta =
        fixedRenyiNumerator N s theta / L ^ theta := by
    unfold fixedRenyiMoment
    rw [Real.rpow_add hL, Real.rpow_one]
    field_simp [hL.ne', (Real.rpow_pos_of_pos hL _).ne']
  have halgebra :
      ((((3 : ℝ) ^ (s + 1)) ^ theta / B ^ theta) *
          ((L / B) ^ (-theta) *
            (∑ c ∈ fixedSet N s,
              ((mapFiberCardAt (fixedSet N s) (cohortEndpoint u) c : ℕ) : ℝ) ^ theta))) =
        (3 : ℝ) ^ theta *
          ((((3 : ℝ) ^ s) ^ theta *
            (∑ c ∈ fixedSet N s,
              ((mapFiberCardAt (fixedSet N s) (cohortEndpoint u) c : ℕ) : ℝ) ^ theta)) /
            L ^ theta) := by
    rw [pow_succ,
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ 3 ^ s) (by norm_num)]
    rw [Real.div_rpow hL.le hB.le]
    rw [Real.rpow_neg hL.le, Real.rpow_neg hB.le]
    have hBp : 0 < B ^ theta := Real.rpow_pos_of_pos hB _
    have hLp : 0 < L ^ theta := Real.rpow_pos_of_pos hL _
    field_simp [hBp.ne', hLp.ne']
  dsimp [L, B, N] at halgebra hlocal hmoment ⊢
  rw [mul_assoc, halgebra, hlocal, ← hmoment]
end CollatzEndpointTransport.FixedTotal
