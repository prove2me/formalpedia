-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiPullbackConstant_le_stage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:25.549138+00:00
-- url     : https://prove2.me/submissions/64c057bc-cf09-4fb6-8c86-a635592e522c

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_lt_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRate_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiShellRate_lt_log_two
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiShellConstant_le_stage
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiDenominatorFloor_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralMomentConstant_pos
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
    {C D theta eta transport : ℝ}
    (hC : 0 < C) (hD0 : 0 < D) (hD1 : D ≤ 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hlinear : transport * D ≤
      centralRenyiShellRate theta transport D / Real.log 2)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8) :
    centralRenyiPullbackConstant C theta eta transport D ≤
      centralRenyiStageConstant theta eta transport *
        (C + 1) * (D⁻¹) ^ 6 := by
  let rate := centralRenyiShellRate theta transport D
  let den := 2 * Real.exp (-rate) - 1
  let floor := centralRenyiDenominatorFloor eta
  have hfloor0 := centralRenyiDenominatorFloor_pos htheta0 heta0 heta1
  have hrate0 : 0 < rate := by
    dsimp [rate, centralRenyiShellRate]
    exact mul_pos (centralRenyiAbsorption_pos htheta0 htransport0)
      (centralRenyiRate_pos htheta0 hD0)
  have hrateLt := centralRenyiShellRate_lt_log_two
    htheta0 htheta1 htransport0 htransport hD0
  have hden0 : 0 < den := by
    dsimp [den]
    have h := Real.exp_lt_exp.mpr (by linarith : -Real.log 2 < -rate)
    have heq : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [heq] at h
    linarith
  have hfloorDen : floor ≤ den := by
    dsimp [floor, centralRenyiDenominatorFloor, den]
    have hexp : Real.exp (-(eta ^ 2 / 8)) ≤ Real.exp (-rate) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hinv : den⁻¹ ≤ floor⁻¹ :=
    (inv_le_inv₀ hden0 hfloor0).2 hfloorDen
  have hshell := centralRenyiShellConstant_le_stage
    hC hD0 hD1 htheta0 htheta1 heta0 heta1 htransport0 htransport
      hlinear hcutParity
  have hstage0 :
      0 ≤ centralRenyiStageShellConstant theta eta transport := by
    unfold centralRenyiStageShellConstant
    have hmoment := centralMomentConstant_pos htheta0 htheta1 heta0 heta1
    have hfactor :
        0 ≤ centralRenyiInverseRateFactor theta transport := by
      unfold centralRenyiInverseRateFactor
      have hz0 := centralRenyiAbsorption_pos htheta0 htransport0
      have hz1 := centralRenyiAbsorption_lt_one htheta0 htransport
      exact pow_nonneg (mul_nonneg
        (div_nonneg (by norm_num) (sub_nonneg.mpr hz1.le))
        (by positivity)) _
    positivity
  unfold centralRenyiPullbackConstant centralRenyiStageConstant
  dsimp [den, floor] at hinv
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    2 * centralRenyiShellConstant C theta eta transport D *
          (2 * Real.exp (-centralRenyiShellRate theta transport D) - 1)⁻¹
        ≤ 2 *
            (centralRenyiStageShellConstant theta eta transport *
              (C + 1) * (D⁻¹) ^ 6) *
            (2 * Real.exp (-centralRenyiShellRate theta transport D) - 1)⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hshell (by norm_num))
        (inv_nonneg.mpr hden0.le)
    _ ≤ 2 *
            (centralRenyiStageShellConstant theta eta transport *
              (C + 1) * (D⁻¹) ^ 6) *
            (centralRenyiDenominatorFloor eta)⁻¹ := by
      have hinner : 0 ≤
          centralRenyiStageShellConstant theta eta transport *
            (C + 1) * (D⁻¹) ^ 6 :=
        mul_nonneg
          (mul_nonneg hstage0 (by linarith : 0 ≤ C + 1))
          (pow_nonneg (inv_nonneg.mpr hD0.le) _)
      exact mul_le_mul_of_nonneg_left hinv
        (mul_nonneg (by norm_num) hinner)
    _ = 2 * centralRenyiStageShellConstant theta eta transport *
          (centralRenyiDenominatorFloor eta)⁻¹ *
          (C + 1) * (D⁻¹) ^ 6 := by
      ring
end CollatzEndpointTransport.FixedTotal
