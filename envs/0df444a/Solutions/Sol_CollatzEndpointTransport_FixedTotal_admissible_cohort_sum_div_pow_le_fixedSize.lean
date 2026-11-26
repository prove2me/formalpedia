-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.admissible_cohort_sum_div_pow_le_fixedSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:21.938981+00:00
-- url     : https://prove2.me/submissions/793c34eb-e2ac-48f6-ad75-a44ed5ff4d48

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralAggregate
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_shell_admissible_fixed_total_aggregate_le_fixedSize
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSizeCentralMomentConstant_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fractionalBinomialMassConstant_pos
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
set_option maxHeartbeats 600000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M : ℕ} (u : Fin M) {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    (∑ s ∈ shellAdmissibleLengthSet M (M - (u : ℕ)) theta eta,
        ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
          fixedRenyiMoment (M - (u : ℕ)) s theta) /
        (2 : ℝ) ^ M ≤
      ((2 : ℝ) ^ (u : ℕ))⁻¹ *
        ((fixedSizeCentralMomentConstant theta eta *
            fractionalBinomialMassConstant theta) *
          (M + 1 : ℝ) ^ (theta / 2)) := by
  let N := M - (u : ℕ)
  let K := fixedSizeCentralMomentConstant theta eta *
    fractionalBinomialMassConstant theta
  have huM : (u : ℕ) ≤ M := Nat.le_of_lt u.isLt
  have hNM : N + (u : ℕ) = M := Nat.sub_add_cancel huM
  have hN : 0 < N := by dsimp [N]; omega
  have hpow : (2 : ℝ) ^ M = (2 : ℝ) ^ (u : ℕ) * (2 : ℝ) ^ N := by
    rw [← pow_add, add_comm, hNM]
  have hnormalize :
      (∑ s ∈ shellAdmissibleLengthSet M N theta eta,
          ((fixedSet N s).card : ℝ) * fixedRenyiMoment N s theta) /
          (2 : ℝ) ^ M =
        ((2 : ℝ) ^ (u : ℕ))⁻¹ *
          (∑ s ∈ shellAdmissibleLengthSet M N theta eta,
            fixedSourceWeight N s * fixedRenyiMoment N s theta) := by
    rw [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    unfold fixedSourceWeight
    rw [hpow]
    field_simp [show (2 : ℝ) ^ (u : ℕ) ≠ 0 by positivity,
      show (2 : ℝ) ^ N ≠ 0 by positivity]
  have hagg := shell_admissible_fixed_total_aggregate_le_fixedSize
    (M := M) (N := N) htheta0 htheta1 heta0 heta1 hN
  have hNle : (N : ℝ) ≤ (M + 1 : ℝ) := by
    exact_mod_cast (Nat.sub_le M (u : ℕ)).trans (Nat.le_succ M)
  have hpowLe : (N : ℝ) ^ (theta / 2) ≤
      (M + 1 : ℝ) ^ (theta / 2) :=
    Real.rpow_le_rpow (by positivity) hNle (by positivity)
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (fixedSizeCentralMomentConstant_pos htheta0 htheta1 heta0 heta1).le
      (fractionalBinomialMassConstant_pos htheta0 htheta1).le
  have hagg' :
      (∑ s ∈ shellAdmissibleLengthSet M N theta eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
        K * (M + 1 : ℝ) ^ (theta / 2) := by
    calc
      _ ≤ K * (N : ℝ) ^ (theta / 2) := by simpa [K] using hagg
      _ ≤ K * (M + 1 : ℝ) ^ (theta / 2) :=
        mul_le_mul_of_nonneg_left hpowLe hK0
  rw [hnormalize]
  exact mul_le_mul_of_nonneg_left hagg' (inv_nonneg.mpr (by positivity))
end CollatzEndpointTransport.FixedTotal
