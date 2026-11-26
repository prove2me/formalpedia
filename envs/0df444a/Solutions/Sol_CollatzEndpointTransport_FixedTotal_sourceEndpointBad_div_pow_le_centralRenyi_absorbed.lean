-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_centralRenyi_absorbed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:52.230857+00:00
-- url     : https://prove2.me/submissions/f54b3565-c605-44b6-a42a-51faf5db6230

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRate_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_centralRenyi_absorbed_large
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
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
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
    (M : ℕ) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      centralRenyiShellConstant C theta eta transport D *
        Real.exp (-centralRenyiShellRate theta transport D * M) := by
  let rate := centralRenyiShellRate theta transport D
  let N0 := centralRenyiStartupIndex theta eta
  have hrate0 : 0 < rate := by
    dsimp [rate, centralRenyiShellRate]
    exact mul_pos (centralRenyiAbsorption_pos htheta0 htransport0)
      (centralRenyiRate_pos htheta0 hS.D_pos)
  by_cases hlarge : centralRenyiStartupScale theta eta ≤ M
  · have h := sourceEndpointBad_div_pow_le_centralRenyi_absorbed_large
      hS htheta0 htheta1 heta0 heta1 htransport0 htransport
      hcutLate hcutParity M hlarge
    have hcoef : centralRenyiLargeShellConstant C theta eta transport D ≤
        centralRenyiShellConstant C theta eta transport D := by
      unfold centralRenyiShellConstant
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    exact h.trans
      (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _))
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
      have hnat' :
          (sourceEndpointBad S M).card ≤ 2 ^ M := by
        calc
          (sourceEndpointBad S M).card ≤ Fintype.card (SourceCode M) := hnat
          _ = 2 ^ M := sourceCode_card M
      have hcast : ((sourceEndpointBad S M).card : ℝ) ≤
          ((2 ^ M : ℕ) : ℝ) := by
        exact_mod_cast hnat'
      simpa using hcast
    have hfrac :
        ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤ 1 :=
      (div_le_one (by positivity)).2 hcard
    have hone :
        1 ≤ Real.exp (rate * N0) * Real.exp (-rate * M) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hlargeNonneg :
        0 ≤ centralRenyiLargeShellConstant C theta eta transport D := by
      unfold centralRenyiLargeShellConstant
      have hmoment := centralMomentConstant_pos htheta0 htheta1 heta0 heta1
      have hterm1 : 0 ≤ 4 * ((eta * Real.log 2 / 16)⁻¹) := by
        positivity
      have hterm2 : 0 ≤ (3 : ℝ) ^ theta *
          centralMomentConstant theta eta *
            (64 * ((((1 - centralRenyiAbsorption theta transport) *
              centralRenyiRate theta D / 6)⁻¹) ^ 6)) := by
        positivity
      nlinarith [hS.C_pos]
    calc
      ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤ 1 := hfrac
      _ ≤ Real.exp (rate * N0) * Real.exp (-rate * M) := hone
      _ ≤ centralRenyiShellConstant C theta eta transport D *
          Real.exp (-rate * M) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        unfold centralRenyiShellConstant
        exact le_add_of_nonneg_left hlargeNonneg
      _ = _ := by rfl
end CollatzEndpointTransport.FixedTotal
