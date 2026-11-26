-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralEndpointInformation_rpow_le_holder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:00:33.126904+00:00
-- url     : https://prove2.me/submissions/11ce3ddb-2ef5-41cb-a5b5-833c77ff4e8a

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiShellTransport
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralEndpointInformation_le_fixedSize
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
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    (centralEndpointInformation M theta eta) ^ (1 / (1 + theta)) ≤
      holderCentralMomentConstant theta eta *
        (M + 1 : ℝ) ^ (theta / (2 * (1 + theta))) := by
  let A := 2 * (3 : ℝ) ^ theta *
    (fixedSizeCentralMomentConstant theta eta *
      fractionalBinomialMassConstant theta)
  have hq : 0 < 1 + theta := by linarith
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
      (mul_pos
        (fixedSizeCentralMomentConstant_pos htheta0 htheta1 heta0 heta1)
        (fractionalBinomialMassConstant_pos htheta0 htheta1))
  have hinfo := centralEndpointInformation_le_fixedSize
    htheta0 htheta1 heta0 heta1 (M := M)
  change centralEndpointInformation M theta eta ≤
    A * (M + 1 : ℝ) ^ (theta / 2) at hinfo
  have hinfo0 : 0 ≤ centralEndpointInformation M theta eta := by
    unfold centralEndpointInformation centralLevelRenyiInformation
    positivity
  have hroot :
      (centralEndpointInformation M theta eta) ^ (1 / (1 + theta)) ≤
        (A * (M + 1 : ℝ) ^ (theta / 2)) ^ (1 / (1 + theta)) :=
    Real.rpow_le_rpow hinfo0 hinfo (by positivity)
  calc
    (centralEndpointInformation M theta eta) ^ (1 / (1 + theta)) ≤
        (A * (M + 1 : ℝ) ^ (theta / 2)) ^
          (1 / (1 + theta)) := hroot
    _ = A ^ (1 / (1 + theta)) *
          ((M + 1 : ℝ) ^ (theta / 2)) ^ (1 / (1 + theta)) := by
      rw [Real.mul_rpow hA.le (Real.rpow_nonneg (by positivity) _)]
    _ = A ^ (1 / (1 + theta)) *
          (M + 1 : ℝ) ^ (theta / (2 * (1 + theta))) := by
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ M + 1)]
      have hexp : (theta / 2) * (1 / (1 + theta)) =
          theta / (2 * (1 + theta)) := by
        field_simp [hq.ne']
      rw [hexp]
    _ = holderCentralMomentConstant theta eta *
          (M + 1 : ℝ) ^ (theta / (2 * (1 + theta))) := by rfl
end CollatzEndpointTransport.FixedTotal
