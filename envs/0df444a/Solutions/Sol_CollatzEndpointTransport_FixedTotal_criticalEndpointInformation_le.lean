-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.criticalEndpointInformation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:46.7946+00:00
-- url     : https://prove2.me/submissions/c4e1ebee-d966-43d6-b890-4ab08fe7d8cf

import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_levelCriticalContribution_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.globalCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) (hM : 1 ≤ M) :
    criticalEndpointInformation M ≤
      9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M := by
  have hpow : (0 : ℝ) < 2 ^ M := by positivity
  have hsum := sum_levelCriticalContribution_le M
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hsqrtM : 1 ≤ Real.sqrt M := by
    simpa using Real.sqrt_le_sqrt hMreal
  have hpowOne : (1 : ℝ) ≤ 2 ^ M := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hdivOne : (1 : ℝ) / 2 ^ M ≤ 1 :=
    (div_le_one hpow).2 hpowOne
  have honeLe : (1 : ℝ) / 2 ^ M ≤ (M : ℝ) * Real.sqrt M := by
    exact hdivOne.trans <|
      one_le_mul_of_one_le_of_one_le hMreal hsqrtM
  unfold criticalEndpointInformation
  calc
    Real.sqrt 3 / (2 ^ M : ℝ) *
        (1 + ∑ s ∈ Finset.Icc 1 M,
          levelCriticalContribution M s) ≤
      Real.sqrt 3 / (2 ^ M : ℝ) *
        (1 + Real.sqrt M * (8 * M * (2 ^ M : ℝ))) := by
      gcongr
    _ ≤ 9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M := by
      have hsqrt3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
      calc
        Real.sqrt 3 / (2 ^ M : ℝ) *
            (1 + Real.sqrt M * (8 * M * (2 ^ M : ℝ))) =
          Real.sqrt 3 * ((1 : ℝ) / 2 ^ M) +
            8 * Real.sqrt 3 * M * Real.sqrt M := by
          field_simp
        _ ≤ Real.sqrt 3 * (M * Real.sqrt M) +
            8 * Real.sqrt 3 * M * Real.sqrt M := by
          gcongr
        _ = 9 * Real.sqrt 3 * M * Real.sqrt M := by ring
end CollatzEndpointTransport.FixedTotal
