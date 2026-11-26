-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_rpow_one_add_le_weighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:46:22.24569+00:00
-- url     : https://prove2.me/submissions/ff6d0a47-9db2-4d2c-bab1-285b4c3e21f8

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
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
open scoped Real
noncomputable section
set_option maxHeartbeats 20000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {ι : Type*} (U : Finset ι) (a w : ι → ℝ)
    {theta : ℝ} (htheta : 0 < theta)
    (ha : ∀ i ∈ U, 0 ≤ a i)
    (hw : ∀ i ∈ U, 0 < w i)
    (hwsum : ∑ i ∈ U, w i ≤ 1) :
    (∑ i ∈ U, a i) ^ (1 + theta) ≤
      ∑ i ∈ U, (w i) ^ (-theta) * (a i) ^ (1 + theta) := by
  let v : ℝ := 1 - ∑ i ∈ U, w i
  have hv : 0 ≤ v := by dsimp [v]; linarith
  have hsum : v + ∑ i ∈ U, w i = 1 := by dsimp [v]; ring
  have hconv := convexOn_rpow (by linarith : 1 ≤ 1 + theta)
  have hj := hconv.map_add_sum_le
    (t := U) (w := w) (p := fun i => a i / w i)
    (v := v) (q := (0 : ℝ))
    (fun i hi => (hw i hi).le) hsum
    (fun i hi => Set.mem_Ici.mpr (div_nonneg (ha i hi) (hw i hi).le))
    hv (Set.mem_Ici.mpr le_rfl)
  have hleft :
      v • (0 : ℝ) + ∑ i ∈ U, w i • (a i / w i) =
        ∑ i ∈ U, a i := by
    simp only [smul_eq_mul, mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_div_cancel₀ (a i) (hw i hi).ne'
  have hright :
      v • ((0 : ℝ) ^ (1 + theta)) +
          ∑ i ∈ U, w i • ((a i / w i) ^ (1 + theta)) =
        ∑ i ∈ U, (w i) ^ (-theta) * (a i) ^ (1 + theta) := by
    have hexp : 1 + theta ≠ 0 := by linarith
    simp only [Real.zero_rpow hexp, smul_eq_mul, mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    have hwi := hw i hi
    by_cases hai : a i = 0
    · simp [hai, hexp]
    · have haiPos : 0 < a i := lt_of_le_of_ne (ha i hi) (Ne.symm hai)
      rw [Real.div_rpow haiPos.le hwi.le]
      rw [Real.rpow_add hwi, Real.rpow_one]
      rw [Real.rpow_neg hwi.le]
      simp only [div_eq_mul_inv, mul_inv_rev]
      change
        w i * (a i ^ (1 + theta) * ((w i ^ theta)⁻¹ * (w i)⁻¹)) =
          (w i ^ theta)⁻¹ * a i ^ (1 + theta)
      calc
        w i * (a i ^ (1 + theta) * ((w i ^ theta)⁻¹ * (w i)⁻¹)) =
            (w i * (w i)⁻¹) *
              ((w i ^ theta)⁻¹ * a i ^ (1 + theta)) := by ring
        _ = (w i ^ theta)⁻¹ * a i ^ (1 + theta) := by
          rw [mul_inv_cancel₀ hwi.ne', one_mul]
  rw [hleft] at hj
  rw [hright] at hj
  exact hj
end CollatzEndpointTransport.FixedTotal
