-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiShellConstant_le_stage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:36.917173+00:00
-- url     : https://prove2.me/submissions/595dab31-2b0e-4cab-b852-b7b45051bf29

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_lt_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiMomentInverse_le
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
    centralRenyiShellConstant C theta eta transport D ≤
      centralRenyiStageShellConstant theta eta transport *
        (C + 1) * (D⁻¹) ^ 6 := by
  let zeta := centralRenyiAbsorption theta transport
  let r := centralRenyiRate theta D
  let A := (3 : ℝ) ^ theta * centralMomentConstant theta eta
  let Z := (D⁻¹) ^ 6
  let B := 3 + 4 * ((eta * Real.log 2 / 16)⁻¹) +
    Real.exp ((eta ^ 2 / 8) * centralRenyiStartupIndex theta eta)
  let Q := A * (64 * centralRenyiInverseRateFactor theta transport)
  have hZ1 : 1 ≤ Z := by
    dsimp [Z]
    exact one_le_pow₀ ((one_le_inv₀ hD0).2 hD1)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (centralMomentConstant_pos htheta0 htheta1 heta0 heta1).le
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hfactor0 :
      0 ≤ centralRenyiInverseRateFactor theta transport := by
    unfold centralRenyiInverseRateFactor
    have hz0 := centralRenyiAbsorption_pos htheta0 htransport0
    have hz1 := centralRenyiAbsorption_lt_one htheta0 htransport
    have hleft :
        0 ≤ 6 / (1 - centralRenyiAbsorption theta transport) :=
      div_nonneg (by norm_num) (sub_nonneg.mpr hz1.le)
    have hright :
        0 ≤ centralRenyiAbsorption theta transport /
          (transport * Real.log 2) := by positivity
    exact pow_nonneg (mul_nonneg hleft hright) _
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg hA0 (mul_nonneg (by norm_num) hfactor0)
  have hmoment := centralRenyiMomentInverse_le
    htheta0 htransport0 htransport hD0 hlinear
  have hmoment' :
      A * (64 * ((((1 - zeta) * r / 6)⁻¹) ^ 6)) ≤ Q * Z := by
    calc
      A * (64 * ((((1 - zeta) * r / 6)⁻¹) ^ 6)) =
          (A * 64) * ((((1 - zeta) * r / 6)⁻¹) ^ 6) := by ring
      _ ≤ (A * 64) *
          (centralRenyiInverseRateFactor theta transport *
            (D⁻¹) ^ 6) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg hA0 (by norm_num))
        simpa [zeta, r] using hmoment
      _ = Q * Z := by dsimp [Q, Z]; ring
  have hstartup :
      Real.exp (centralRenyiShellRate theta transport D *
          centralRenyiStartupIndex theta eta) ≤
        Real.exp ((eta ^ 2 / 8) *
          centralRenyiStartupIndex theta eta) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hcutParity (by positivity)
  have hshell :
      centralRenyiShellConstant C theta eta transport D ≤
        C + B + Q * Z := by
    unfold centralRenyiShellConstant centralRenyiLargeShellConstant
    calc
      C + 2 + 4 * (eta * Real.log 2 / 16)⁻¹ +
              3 ^ theta * centralMomentConstant theta eta *
                (64 * (((1 - centralRenyiAbsorption theta transport) *
                  centralRenyiRate theta D / 6)⁻¹ ^ 6)) +
            Real.exp (centralRenyiShellRate theta transport D *
              centralRenyiStartupIndex theta eta)
          ≤ C + 2 + 4 * (eta * Real.log 2 / 16)⁻¹ + Q * Z +
            Real.exp ((eta ^ 2 / 8) *
              centralRenyiStartupIndex theta eta) := by
        gcongr
      _ ≤ C + B + Q * Z := by
        dsimp [B]
        linarith
  have hmajor :
      C + B + Q * Z ≤ (1 + B + Q) * (C + 1) * Z := by
    have hC1 : 0 ≤ C + 1 := by linarith
    have hZ0 : 0 ≤ Z := by linarith
    have hCB0 : 0 ≤ C + B := by linarith
    have hfirst : C + B + Q * Z ≤ (C + B + Q) * Z := by
      nlinarith [mul_nonneg hCB0 (sub_nonneg.mpr hZ1)]
    have hcoef : C + B + Q ≤ (1 + B + Q) * (C + 1) := by
      nlinarith [mul_nonneg hB0 hC.le, mul_nonneg hQ0 hC.le]
    exact hfirst.trans (mul_le_mul_of_nonneg_right hcoef hZ0)
  have hstage :
      centralRenyiStageShellConstant theta eta transport = 1 + B + Q := by
    dsimp [centralRenyiStageShellConstant, B, Q, A]
    ring
  change centralRenyiShellConstant C theta eta transport D ≤
    centralRenyiStageShellConstant theta eta transport * (C + 1) * Z
  rw [hstage]
  exact hshell.trans hmajor
end CollatzEndpointTransport.FixedTotal
