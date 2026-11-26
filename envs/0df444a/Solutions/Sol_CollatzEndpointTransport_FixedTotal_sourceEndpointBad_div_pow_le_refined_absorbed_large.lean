-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_refined_absorbed_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:17.667737+00:00
-- url     : https://prove2.me/submissions/e03724d8-c3cd-440b-8db9-0234114fc507

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_holderTargetExponent_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_holderScaleExponent_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_refinedCentralRenyiInverseRateFactor_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_refinedCentralRenyiMomentInverse_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_targetBinomialFront_rpow_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_refined_startup
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_refinedCentralRenyiLargeShellConstant_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_lt_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRate_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyi_lateDiscardRatio_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyi_startup
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_holderCentralMomentConstant_pos
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
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_rpow_succ_mul_exp_neg_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_succ_mul_exp_neg_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_zero
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_C_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_D_le_one
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_D_pos
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
    {S : Set ℕ} {C D theta eta transport : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hlinear : transport * D ≤
      centralRenyiShellRate theta transport D / Real.log 2)
    (hcutLate : centralRenyiShellRate theta transport D ≤
      eta * Real.log 2 / 16)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8)
    (M : ℕ) (hM : centralRenyiStartupScale theta eta ≤ M) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      refinedCentralRenyiLargeShellConstant theta eta transport *
        (1 + C ^ holderTargetExponent theta) *
        (D⁻¹) ^ holderScaleExponent theta *
        Real.exp (-centralRenyiShellRate theta transport D * M) := by
  let B := holderScaleExponent theta
  let rho := holderTargetExponent theta
  let r := centralRenyiRate theta D
  let zeta := centralRenyiAbsorption theta transport
  let rs := centralRenyiShellRate theta transport D
  let rL := eta * Real.log 2 / 8
  let A := holderCentralMomentConstant theta eta
  let Q := refinedCentralRenyiInverseRateFactor theta transport
  let Z := (D⁻¹) ^ B
  have hB : 0 < B := holderScaleExponent_pos htheta0
  have hrho : 0 < rho := holderTargetExponent_pos htheta0
  have hr : 0 < r := centralRenyiRate_pos htheta0 hS.D_pos
  have hz0 : 0 < zeta := centralRenyiAbsorption_pos htheta0 htransport0
  have hz1 : zeta < 1 := centralRenyiAbsorption_lt_one htheta0 htransport
  have hrs : rs = zeta * r := rfl
  have hrL : 0 < rL := by dsimp [rL]; positivity
  have hA : 0 < A := by
    dsimp [A]
    exact holderCentralMomentConstant_pos htheta0 htheta1 heta0 heta1
  have hQ : 0 < Q := by
    dsimp [Q]
    exact refinedCentralRenyiInverseRateFactor_pos
      htheta0 htransport0 htransport
  have hZ1 : 1 ≤ Z := by
    dsimp [Z, B]
    exact Real.one_le_rpow ((one_le_inv₀ hS.D_pos).2 hS.D_le_one)
      (holderScaleExponent_pos htheta0).le
  have hZ0 : 0 ≤ Z := hZ1.trans' (by norm_num)
  have hM1 : (1 : ℝ) ≤ M := by
    have hscale : (4 : ℝ) ≤ centralRenyiStartupScale theta eta := by
      unfold centralRenyiStartupScale
      exact le_max_left _ _
    exact (show (1 : ℝ) ≤ 4 by norm_num).trans (hscale.trans hM)
  have hstart := sourceEndpointBad_div_pow_le_refined_startup
    hS htheta0 htheta1 heta0 heta1 M hM
  obtain ⟨hKM, _, _, _⟩ := centralRenyi_startup htheta0 heta0 heta1 hM
  have hlateRaw := centralRenyi_lateDiscardRatio_le eta M hKM
  have hlateAbs :
      (((((M + 1) * 2 ^ (M - centralRenyiDiscardDepth eta M) : ℕ) : ℝ) /
          (2 ^ M : ℝ))) ≤
        4 * ((eta * Real.log 2 / 16)⁻¹) * Real.exp (-rs * M) := by
    have hpoly := succ_mul_exp_neg_le hrL (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hM1
    have hhalfRate : (1 / 2 : ℝ) * rL = eta * Real.log 2 / 16 := by
      dsimp [rL]
      ring
    have hrate : rs ≤ (1 / 2 : ℝ) * rL := by
      rw [hhalfRate]
      exact hcutLate
    have hexp : Real.exp (-((1 / 2 : ℝ) * rL) * M) ≤
        Real.exp (-rs * M) := by
      apply Real.exp_le_exp.mpr
      nlinarith [show 0 ≤ (M : ℝ) by positivity]
    calc
      (((((M + 1) * 2 ^ (M - centralRenyiDiscardDepth eta M) : ℕ) : ℝ) /
          (2 ^ M : ℝ))) ≤
          2 * (M + 1 : ℝ) * Real.exp (-rL * M) := by
            simpa [rL] using hlateRaw
      _ ≤ 2 * (2 * (((1 - (1 / 2 : ℝ)) * rL)⁻¹) *
          Real.exp (-((1 / 2 : ℝ) * rL) * M)) := by
            rw [show 2 * (M + 1 : ℝ) * Real.exp (-rL * M) =
              2 * ((M + 1 : ℝ) * Real.exp (-rL * M)) by ring]
            exact mul_le_mul_of_nonneg_left hpoly (by norm_num)
      _ = 4 * ((eta * Real.log 2 / 16)⁻¹) *
          Real.exp (-((1 / 2 : ℝ) * rL) * M) := by
            rw [hhalfRate]
            ring
      _ ≤ 4 * ((eta * Real.log 2 / 16)⁻¹) * Real.exp (-rs * M) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
  have hparity :
      2 * Real.exp (-2 * (eta / 4) ^ 2 * M) ≤
        2 * Real.exp (-rs * M) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hcutParity
      (show 0 ≤ (M : ℝ) by positivity)
    have hneg := neg_le_neg hmul
    simpa [rs, show 2 * (eta / 4) ^ 2 = eta ^ 2 / 8 by ring] using hneg
  have htarget :
      (C * Real.exp (-D * Real.log 3)) ^ rho ≤ C ^ rho := by
    simpa [rho] using targetBinomialFront_rpow_le
      hS.C_pos hS.D_pos htheta0
  have hmomentInverse := refinedCentralRenyiMomentInverse_le
    htheta0 htransport0 htransport hS.D_pos hlinear
  have hmoment :
      (C * Real.exp (-D * Real.log 3)) ^ rho * A *
          (M + 1 : ℝ) ^ B * Real.exp (-r * M) ≤
        (C ^ rho * A * ((2 : ℝ) ^ B * Q) * Z) *
          Real.exp (-rs * M) := by
    have hp := rpow_succ_mul_exp_neg_le hB hr hz0 hz1 hM1
    have hpD :
        (M + 1 : ℝ) ^ B * Real.exp (-r * M) ≤
          ((2 : ℝ) ^ B * Q * Z) * Real.exp (-rs * M) := by
      calc
        (M + 1 : ℝ) ^ B * Real.exp (-r * M) ≤
            (2 : ℝ) ^ B * (((1 - zeta) * r / B) ^ (-B)) *
              Real.exp (-(zeta * r) * M) := hp
        _ ≤ (2 : ℝ) ^ B * (Q * Z) *
              Real.exp (-(zeta * r) * M) := by
          have hmid : (((1 - zeta) * r / B) ^ (-B)) ≤ Q * Z := by
            simpa [zeta, r, B, Q, Z] using hmomentInverse
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmid
              (Real.rpow_nonneg (by norm_num) _))
            (Real.exp_nonneg _)
        _ = ((2 : ℝ) ^ B * Q * Z) * Real.exp (-rs * M) := by
          rw [hrs]
          ring
    have hfront0 : 0 ≤
        (C * Real.exp (-D * Real.log 3)) ^ rho * A :=
      mul_nonneg
        (Real.rpow_nonneg
          (mul_pos hS.C_pos (Real.exp_pos _)).le _)
        hA.le
    calc
      (C * Real.exp (-D * Real.log 3)) ^ rho * A *
          (M + 1 : ℝ) ^ B * Real.exp (-r * M) =
        ((C * Real.exp (-D * Real.log 3)) ^ rho * A) *
          ((M + 1 : ℝ) ^ B * Real.exp (-r * M)) := by ring
      _ ≤ ((C * Real.exp (-D * Real.log 3)) ^ rho * A) *
          (((2 : ℝ) ^ B * Q * Z) * Real.exp (-rs * M)) :=
        mul_le_mul_of_nonneg_left hpD hfront0
      _ ≤ (C ^ rho * A) *
          (((2 : ℝ) ^ B * Q * Z) * Real.exp (-rs * M)) := by
        gcongr
      _ = (C ^ rho * A * ((2 : ℝ) ^ B * Q) * Z) *
          Real.exp (-rs * M) := by ring
  let L := refinedCentralRenyiLargeShellConstant theta eta transport
  have hL : 0 < L := refinedCentralRenyiLargeShellConstant_pos
    htheta0 htheta1 heta0 heta1 htransport0 htransport
  have hmajor :
      (4 * ((eta * Real.log 2 / 16)⁻¹) + 2 +
          C ^ rho * A * ((2 : ℝ) ^ B * Q) * Z) *
          Real.exp (-rs * M) ≤
        L * (1 + C ^ rho) * Z * Real.exp (-rs * M) := by
    have hCrho0 : 0 ≤ C ^ rho := Real.rpow_nonneg hS.C_pos.le _
    have hbase0 : 0 ≤ 4 * ((eta * Real.log 2 / 16)⁻¹) + 2 := by
      positivity
    have hAQ0 : 0 ≤ A * ((2 : ℝ) ^ B * Q) := by positivity
    have hcoef :
        4 * ((eta * Real.log 2 / 16)⁻¹) + 2 +
            C ^ rho * A * ((2 : ℝ) ^ B * Q) * Z ≤
          L * (1 + C ^ rho) * Z := by
      dsimp [L, refinedCentralRenyiLargeShellConstant]
      nlinarith [mul_nonneg hbase0 (sub_nonneg.mpr hZ1),
        mul_nonneg hAQ0 (mul_nonneg hCrho0 (sub_nonneg.mpr hZ1))]
    exact mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
  calc
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
        (((((M + 1) * 2 ^ (M - centralRenyiDiscardDepth eta M) : ℕ) : ℝ) /
            (2 ^ M : ℝ)) +
          2 * Real.exp (-2 * (eta / 4) ^ 2 * M) +
          (C * Real.exp (-D * Real.log 3)) ^ rho * A *
            (M + 1 : ℝ) ^ B * Real.exp (-r * M)) := by
      simpa [A, B, rho, r] using hstart
    _ ≤ (4 * ((eta * Real.log 2 / 16)⁻¹) + 2 +
          C ^ rho * A * ((2 : ℝ) ^ B * Q) * Z) *
          Real.exp (-rs * M) := by
      exact (add_le_add (add_le_add hlateAbs hparity) hmoment).trans_eq (by ring)
    _ ≤ L * (1 + C ^ rho) * Z * Real.exp (-rs * M) := hmajor
    _ = _ := by rfl
end CollatzEndpointTransport.FixedTotal
