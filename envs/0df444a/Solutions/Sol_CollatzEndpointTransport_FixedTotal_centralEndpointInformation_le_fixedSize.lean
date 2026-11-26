-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralEndpointInformation_le_fixedSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:40.788055+00:00
-- url     : https://prove2.me/submissions/c31a6a49-3243-4008-b814-b4541438e80d

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralAggregate
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_admissible_cohort_sum_div_pow_le_fixedSize
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelRenyiInformation_le_sharp
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
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_active_central_cohorts_eq_admissible_lengths
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fin_two_pow_inv_le_two
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
    {M : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    centralEndpointInformation M theta eta ≤
      2 * (3 : ℝ) ^ theta *
        (fixedSizeCentralMomentConstant theta eta *
          fractionalBinomialMassConstant theta) *
        (M + 1 : ℝ) ^ (theta / 2) := by
  classical
  unfold centralEndpointInformation
  have hlevels :
      ∑ s ∈ Finset.range (M + 1),
          centralLevelRenyiInformation M s theta eta ≤
        (3 : ℝ) ^ theta *
          ∑ s ∈ Finset.range (M + 1),
            ∑ u ∈ activeMixtureIndices (Finset.univ : Finset (Fin M))
                (centralLevelCohortSet M s theta eta),
              ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
                fixedRenyiMoment (M - (u : ℕ)) s theta := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    exact centralLevelRenyiInformation_le_sharp htheta0
      (Nat.le_of_lt_succ (Finset.mem_range.mp hs))
  have hreindex := sum_active_central_cohorts_eq_admissible_lengths M theta eta
    (fun u s => ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
      fixedRenyiMoment (M - (u : ℕ)) s theta)
  have hpow : 0 < (2 : ℝ) ^ M := by positivity
  let K := fixedSizeCentralMomentConstant theta eta *
    fractionalBinomialMassConstant theta
  apply (div_le_iff₀ hpow).2
  calc
    ∑ s ∈ Finset.range (M + 1),
        centralLevelRenyiInformation M s theta eta ≤
      (3 : ℝ) ^ theta *
        ∑ s ∈ Finset.range (M + 1),
          ∑ u ∈ activeMixtureIndices (Finset.univ : Finset (Fin M))
              (centralLevelCohortSet M s theta eta),
            ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
              fixedRenyiMoment (M - (u : ℕ)) s theta := hlevels
    _ = (3 : ℝ) ^ theta *
        ∑ u : Fin M,
          ∑ s ∈ shellAdmissibleLengthSet M (M - (u : ℕ)) theta eta,
            ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
              fixedRenyiMoment (M - (u : ℕ)) s theta := by rw [hreindex]
    _ ≤ (3 : ℝ) ^ theta *
        ∑ u : Fin M,
          ((2 : ℝ) ^ M * (((2 : ℝ) ^ (u : ℕ))⁻¹ *
            (K * (M + 1 : ℝ) ^ (theta / 2)))) := by
      gcongr with u
      have hu := admissible_cohort_sum_div_pow_le_fixedSize u
        htheta0 htheta1 heta0 heta1
      simpa [K, mul_assoc, mul_comm, mul_left_comm] using
        (div_le_iff₀ hpow).mp hu
    _ = (2 : ℝ) ^ M *
        ((3 : ℝ) ^ theta * (K * (M + 1 : ℝ) ^ (theta / 2)) *
          (∑ u : Fin M, ((2 : ℝ) ^ (u : ℕ))⁻¹)) := by
      conv_lhs => rw [Finset.mul_sum]
      calc
        ∑ u : Fin M,
            (3 : ℝ) ^ theta *
              ((2 : ℝ) ^ M * (((2 : ℝ) ^ (u : ℕ))⁻¹ *
                (K * (M + 1 : ℝ) ^ (theta / 2)))) =
          ∑ u : Fin M,
            ((2 : ℝ) ^ M * ((3 : ℝ) ^ theta *
              (K * (M + 1 : ℝ) ^ (theta / 2)))) *
              ((2 : ℝ) ^ (u : ℕ))⁻¹ := by
            apply Finset.sum_congr rfl
            intro u hu
            ring
        _ = ((2 : ℝ) ^ M * ((3 : ℝ) ^ theta *
              (K * (M + 1 : ℝ) ^ (theta / 2)))) *
              (∑ u : Fin M, ((2 : ℝ) ^ (u : ℕ))⁻¹) := by
            rw [Finset.mul_sum]
        _ = _ := by ring
    _ ≤ (2 : ℝ) ^ M *
        (2 * (3 : ℝ) ^ theta * K *
          (M + 1 : ℝ) ^ (theta / 2)) := by
      have hsum := sum_fin_two_pow_inv_le_two M
      have hcoef : 0 ≤ (3 : ℝ) ^ theta *
          (K * (M + 1 : ℝ) ^ (theta / 2)) := by
        have hK0 : 0 ≤ K := by
          dsimp [K]
          exact mul_nonneg
            (fixedSizeCentralMomentConstant_pos
              htheta0 htheta1 heta0 heta1).le
            (fractionalBinomialMassConstant_pos htheta0 htheta1).le
        exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (mul_nonneg hK0 (Real.rpow_nonneg (by positivity) _))
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (3 : ℝ) ^ theta * (K * (M + 1 : ℝ) ^ (theta / 2)) *
            (∑ u : Fin M, ((2 : ℝ) ^ (u : ℕ))⁻¹) ≤
          (3 : ℝ) ^ theta * (K * (M + 1 : ℝ) ^ (theta / 2)) * 2 :=
        mul_le_mul_of_nonneg_left hsum hcoef
        _ = 2 * (3 : ℝ) ^ theta * K *
            (M + 1 : ℝ) ^ (theta / 2) := by ring
    _ = (2 * (3 : ℝ) ^ theta *
          (fixedSizeCentralMomentConstant theta eta *
            fractionalBinomialMassConstant theta) *
          (M + 1 : ℝ) ^ (theta / 2)) * (2 : ℝ) ^ M := by
      dsimp [K]
      ring
end CollatzEndpointTransport.FixedTotal
