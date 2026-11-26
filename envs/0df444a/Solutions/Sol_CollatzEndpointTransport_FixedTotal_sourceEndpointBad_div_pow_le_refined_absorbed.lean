-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_refined_absorbed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:12:54.199987+00:00
-- url     : https://prove2.me/submissions/22576a41-87cb-405d-8df0-6868a98bae3c

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_holderScaleExponent_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_refinedCentralRenyiLargeShellConstant_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_refined_absorbed_large
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_refinedCentralRenyiShellConstant_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRate_pos
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
    (M : ℕ) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      refinedCentralRenyiShellConstant theta eta transport *
        (1 + C ^ holderTargetExponent theta) *
        (D⁻¹) ^ holderScaleExponent theta *
        Real.exp (-centralRenyiShellRate theta transport D * M) := by
  let rs := centralRenyiShellRate theta transport D
  let N0 := centralRenyiStartupIndex theta eta
  have hrs0 : 0 < rs := by
    dsimp [rs, centralRenyiShellRate]
    exact mul_pos (centralRenyiAbsorption_pos htheta0 htransport0)
      (centralRenyiRate_pos htheta0 hS.D_pos)
  by_cases hlarge : centralRenyiStartupScale theta eta ≤ M
  · have h := sourceEndpointBad_div_pow_le_refined_absorbed_large
      hS htheta0 htheta1 heta0 heta1 htransport0 htransport
      hlinear hcutLate hcutParity M hlarge
    have hcoef :
        refinedCentralRenyiLargeShellConstant theta eta transport ≤
          refinedCentralRenyiShellConstant theta eta transport := by
      unfold refinedCentralRenyiShellConstant
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    exact h.trans (by
      gcongr
      · exact Real.rpow_nonneg (inv_nonneg.mpr hS.D_pos.le) _
      · exact add_nonneg (by norm_num) (Real.rpow_nonneg hS.C_pos.le _))
  · have hscaleCeil : centralRenyiStartupScale theta eta ≤ N0 := by
      dsimp [N0, centralRenyiStartupIndex]
      exact Nat.le_ceil _
    have hMN0 : (M : ℝ) ≤ N0 := by
      by_contra hnot
      have hN0M : (N0 : ℝ) < M := lt_of_not_ge hnot
      exact hlarge (hscaleCeil.trans hN0M.le)
    have hcard : ((sourceEndpointBad S M).card : ℝ) ≤ 2 ^ M := by
      have hnat :
          (sourceEndpointBad S M).card ≤ Fintype.card (SourceCode M) :=
        Finset.card_le_univ _
      have hnat' : (sourceEndpointBad S M).card ≤ 2 ^ M := by
        calc
          (sourceEndpointBad S M).card ≤ Fintype.card (SourceCode M) := hnat
          _ = 2 ^ M := sourceCode_card M
      exact_mod_cast hnat'
    have hfrac :
        ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).2 hcard
    have hone :
        1 ≤ Real.exp ((eta ^ 2 / 8) * N0) * Real.exp (-rs * M) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hrateN : rs * N0 ≤ (eta ^ 2 / 8) * N0 :=
        mul_le_mul_of_nonneg_right hcutParity (by positivity)
      nlinarith
    have hfront : 1 ≤
        (1 + C ^ holderTargetExponent theta) *
          (D⁻¹) ^ holderScaleExponent theta := by
      have hCrho0 : 0 ≤ C ^ holderTargetExponent theta :=
        Real.rpow_nonneg hS.C_pos.le _
      have hZ1 : 1 ≤ (D⁻¹) ^ holderScaleExponent theta :=
        Real.one_le_rpow ((one_le_inv₀ hS.D_pos).2 hS.D_le_one)
          (holderScaleExponent_pos htheta0).le
      nlinarith
    have hlargeNonneg : 0 ≤
        refinedCentralRenyiLargeShellConstant theta eta transport :=
      (refinedCentralRenyiLargeShellConstant_pos
        htheta0 htheta1 heta0 heta1 htransport0 htransport).le
    calc
      ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤ 1 := hfrac
      _ ≤ Real.exp ((eta ^ 2 / 8) * N0) * Real.exp (-rs * M) := hone
      _ ≤ refinedCentralRenyiShellConstant theta eta transport *
          Real.exp (-rs * M) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        unfold refinedCentralRenyiShellConstant
        exact le_add_of_nonneg_left hlargeNonneg
      _ ≤ refinedCentralRenyiShellConstant theta eta transport *
          ((1 + C ^ holderTargetExponent theta) *
            (D⁻¹) ^ holderScaleExponent theta) *
          Real.exp (-rs * M) := by
        have hconst0 := (refinedCentralRenyiShellConstant_pos
          htheta0 htheta1 heta0 heta1 htransport0 htransport).le
        nlinarith [mul_nonneg hconst0 (sub_nonneg.mpr hfront), Real.exp_pos (-rs * M)]
      _ = _ := by ring
end CollatzEndpointTransport.FixedTotal
