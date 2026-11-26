-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.shell_admissible_fixed_total_aggregate_le_fixedSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:54:46.83432+00:00
-- url     : https://prove2.me/submissions/57c0566a-112e-4c04-b9f8-dd16369b3cfb

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralAggregate
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSizeCentralMomentConstant_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_mul_fixedRenyiMoment_le_fixedSize
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_nonneg
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
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fixedSourceWeight_rpow_central_le
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
    {M N : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (hN : 0 < N) :
    (∑ s ∈ shellAdmissibleLengthSet M N theta eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
      (fixedSizeCentralMomentConstant theta eta *
          fractionalBinomialMassConstant theta) *
        (N : ℝ) ^ (theta / 2) := by
  classical
  let U := shellAdmissibleLengthSet M N theta eta
  let K := fixedSizeCentralMomentConstant theta eta
  by_cases hU : U = ∅
  · simp [U, hU]
    exact mul_nonneg
      (mul_nonneg
        (fixedSizeCentralMomentConstant_pos htheta0 htheta1 heta0 heta1).le
        (fractionalBinomialMassConstant_pos htheta0 htheta1).le)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hUNonempty : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
  obtain ⟨s0, hs0⟩ := hUNonempty
  have hadm0 : CentralRenyiAdmissible N s0 theta eta :=
    (Finset.mem_filter.mp hs0).2
  have hN2 : 2 < N := by
    unfold CentralRenyiAdmissible at hadm0
    omega
  have hK0 : 0 ≤ K :=
    (fixedSizeCentralMomentConstant_pos htheta0 htheta1 heta0 heta1).le
  have hlevel : ∀ s ∈ U,
      fixedSourceWeight N s * fixedRenyiMoment N s theta ≤
        K * (fixedSourceWeight N s) ^ (1 - theta) := by
    intro s hs
    have hadm : CentralRenyiAdmissible N s theta eta :=
      (Finset.mem_filter.mp hs).2
    exact fixedSourceWeight_mul_fixedRenyiMoment_le_fixedSize
      htheta0 htheta1 heta0 heta1 hN2
      hadm.2.1 hadm.2.2.1 hadm.2.2.2.1
      hadm.2.2.2.2.1 hadm.2.2.2.2.2
  have hsub : U ⊆ centralLengthSet N eta := by
    intro s hs
    have hadm : CentralRenyiAdmissible N s theta eta :=
      (Finset.mem_filter.mp hs).2
    rw [centralLengthSet, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr
      ⟨Nat.le_of_lt hadm.2.1, Nat.le_of_lt hadm.2.2.1⟩,
      hadm.2.2.2.1⟩
  have hpowersSubset :
      (∑ s ∈ U, (fixedSourceWeight N s) ^ (1 - theta)) ≤
        ∑ s ∈ centralLengthSet N eta,
          (fixedSourceWeight N s) ^ (1 - theta) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun s hs hnot => Real.rpow_nonneg (fixedSourceWeight_nonneg N s) _)
  have hpowersCentral := sum_fixedSourceWeight_rpow_central_le
    (N := N) (theta := theta) (eta := eta) (by omega) htheta0 htheta1
  have hpowers :
      (∑ s ∈ U, (fixedSourceWeight N s) ^ (1 - theta)) ≤
        fractionalBinomialMassConstant theta *
          (N : ℝ) ^ (theta / 2) :=
    hpowersSubset.trans hpowersCentral
  calc
    (∑ s ∈ shellAdmissibleLengthSet M N theta eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
        ∑ s ∈ U, K * (fixedSourceWeight N s) ^ (1 - theta) := by
      simpa [U] using Finset.sum_le_sum hlevel
    _ = K * ∑ s ∈ U, (fixedSourceWeight N s) ^ (1 - theta) := by
      rw [Finset.mul_sum]
    _ ≤ K * (fractionalBinomialMassConstant theta *
          (N : ℝ) ^ (theta / 2)) :=
      mul_le_mul_of_nonneg_left hpowers hK0
    _ = (fixedSizeCentralMomentConstant theta eta *
          fractionalBinomialMassConstant theta) *
        (N : ℝ) ^ (theta / 2) := by
      dsimp [K]
      ring
end CollatzEndpointTransport.FixedTotal
