-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_centralRenyi_absorbed_large_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:04:38.439298+00:00
-- url     : https://prove2.me/submissions/05fdf577-21b3-48ab-a5f8-5fc34dd7fa89

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_rpow_succ_mul_exp_neg_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_centralRenyi_startup_sharp
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralMomentConstant_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_lt_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRate_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyi_lateDiscardRatio_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyi_startup
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
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_succ_mul_exp_neg_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_zero
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_C_pos
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
open Nat Finset
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
    (hcutLate : centralRenyiShellRate theta transport D ≤
      eta * Real.log 2 / 16)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8)
    (M : ℕ) (hM : centralRenyiStartupScale theta eta ≤ M) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      sharpCentralRenyiLargeShellConstant C theta eta transport D *
        Real.exp (-centralRenyiShellRate theta transport D * M) := by
  let B := 1 + theta
  let r := centralRenyiRate theta D
  let zeta := centralRenyiAbsorption theta transport
  let rs := centralRenyiShellRate theta transport D
  let rL := eta * Real.log 2 / 8
  let A := 2 * (3 : ℝ) ^ theta * centralMomentConstant theta eta
  have hB : 0 < B := by dsimp [B]; linarith
  have hr : 0 < r := centralRenyiRate_pos htheta0 hS.D_pos
  have hz0 : 0 < zeta := centralRenyiAbsorption_pos htheta0 htransport0
  have hz1 : zeta < 1 := centralRenyiAbsorption_lt_one htheta0 htransport
  have hrs : rs = zeta * r := rfl
  have hrL : 0 < rL := by dsimp [rL]; positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
      (centralMomentConstant_pos htheta0 htheta1 heta0 heta1).le
  have hM1 : (1 : ℝ) ≤ M := by
    have hscale : (4 : ℝ) ≤ centralRenyiStartupScale theta eta := by
      unfold centralRenyiStartupScale
      exact le_max_left _ _
    exact (show (1 : ℝ) ≤ 4 by norm_num).trans (hscale.trans hM)
  have hstart := sourceEndpointBad_div_pow_le_centralRenyi_startup_sharp
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
      2 * Real.exp (-2 * (eta / 4) ^ 2 * M) ≤ 2 * Real.exp (-rs * M) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hcutParity
      (show 0 ≤ (M : ℝ) by positivity)
    have hneg := neg_le_neg hmul
    simpa [rs, show 2 * (eta / 4) ^ 2 = eta ^ 2 / 8 by ring] using hneg
  have hcentralExp : Real.exp (-r * M) ≤ Real.exp (-rs * M) := by
    apply Real.exp_le_exp.mpr
    have hzr : zeta * r ≤ r := mul_le_of_le_one_left hr.le hz1.le
    have hneg := neg_le_neg (mul_le_mul_of_nonneg_right hzr
      (show 0 ≤ (M : ℝ) by positivity))
    simpa [hrs, mul_assoc] using hneg
  have htarget :
      C * Real.exp (-D * Real.log 3) * Real.exp (-r * M) ≤
        C * Real.exp (-rs * M) := by
    have hq : Real.exp (-D * Real.log 3) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hS.D_pos.le)
        (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le
    calc
      C * Real.exp (-D * Real.log 3) * Real.exp (-r * M) ≤
          C * 1 * Real.exp (-r * M) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq hS.C_pos.le) (Real.exp_nonneg _)
      _ = C * Real.exp (-r * M) := by ring
      _ ≤ C * Real.exp (-rs * M) :=
        mul_le_mul_of_nonneg_left hcentralExp hS.C_pos.le
  have hmoment :
      A * (M + 1 : ℝ) ^ B * Real.exp (-r * M) ≤
        (A * ((2 : ℝ) ^ B * (((1 - zeta) * r / B) ^ (-B)))) *
          Real.exp (-rs * M) := by
    have hp := rpow_succ_mul_exp_neg_le hB hr hz0 hz1 hM1
    rw [hrs]
    calc
      A * (M + 1 : ℝ) ^ B * Real.exp (-r * M) =
          A * ((M + 1 : ℝ) ^ B * Real.exp (-r * M)) := by ring
      _ ≤ A * ((2 : ℝ) ^ B * (((1 - zeta) * r / B) ^ (-B)) *
            Real.exp (-(zeta * r) * M)) :=
        mul_le_mul_of_nonneg_left hp hA
      _ = (A * ((2 : ℝ) ^ B * (((1 - zeta) * r / B) ^ (-B)))) *
          Real.exp (-(zeta * r) * M) := by ring
  have hcentral :
      (C * Real.exp (-D * Real.log 3) + A * (M + 1 : ℝ) ^ B) *
          Real.exp (-r * M) ≤
        (C + A * ((2 : ℝ) ^ B * (((1 - zeta) * r / B) ^ (-B)))) *
          Real.exp (-rs * M) := by
    rw [add_mul, add_mul]
    exact add_le_add htarget hmoment
  calc
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
        (((((M + 1) * 2 ^ (M - centralRenyiDiscardDepth eta M) : ℕ) : ℝ) /
            (2 ^ M : ℝ)) +
          2 * Real.exp (-2 * (eta / 4) ^ 2 * M) +
          (C * Real.exp (-D * Real.log 3) + A * (M + 1 : ℝ) ^ B) *
            Real.exp (-r * M)) := by
      simpa [A, B, r] using hstart
    _ ≤ (4 * ((eta * Real.log 2 / 16)⁻¹) + 2 + C +
          A * ((2 : ℝ) ^ B * (((1 - zeta) * r / B) ^ (-B)))) *
          Real.exp (-rs * M) := by
      exact (add_le_add (add_le_add hlateAbs hparity) hcentral).trans_eq (by ring)
    _ = sharpCentralRenyiLargeShellConstant C theta eta transport D *
          Real.exp (-centralRenyiShellRate theta transport D * M) := by
      dsimp [sharpCentralRenyiLargeShellConstant, A, B, r, zeta, rs]
      ring
end CollatzEndpointTransport.FixedTotal
