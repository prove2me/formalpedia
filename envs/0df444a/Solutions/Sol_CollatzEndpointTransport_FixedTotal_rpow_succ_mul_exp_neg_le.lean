-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.rpow_succ_mul_exp_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:21:03.409251+00:00
-- url     : https://prove2.me/submissions/38427bc6-d8fc-4021-9ba5-4c7e54f15451

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
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {B r zeta x : ℝ}
    (hB : 0 < B) (hr : 0 < r)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hx : 1 ≤ x) :
    (x + 1) ^ B * Real.exp (-r * x) ≤
      (2 : ℝ) ^ B * (((1 - zeta) * r / B) ^ (-B)) *
        Real.exp (-(zeta * r) * x) := by
  let a := (1 - zeta) * r / B
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (mul_pos (sub_pos.mpr hzeta1) hr) hB
  have hax : a * x ≤ Real.exp (a * x) := by
    nlinarith [Real.add_one_le_exp (a * x)]
  have hxexp : x ≤ a⁻¹ * Real.exp (a * x) := by
    calc
      x = a⁻¹ * (a * x) := by field_simp [ha.ne']
      _ ≤ a⁻¹ * Real.exp (a * x) :=
        mul_le_mul_of_nonneg_left hax (inv_nonneg.mpr ha.le)
  have hsucc : x + 1 ≤ 2 * x := by linarith
  have hbase : x + 1 ≤ 2 * (a⁻¹ * Real.exp (a * x)) :=
    hsucc.trans (mul_le_mul_of_nonneg_left hxexp (by norm_num))
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ x + 1) hbase hB.le
  have hpow' :
      (x + 1) ^ B ≤
        (2 : ℝ) ^ B * a ^ (-B) * Real.exp (B * (a * x)) := by
    calc
      (x + 1) ^ B ≤ (2 * (a⁻¹ * Real.exp (a * x))) ^ B := hpow
      _ = (2 : ℝ) ^ B * a ^ (-B) * Real.exp (B * (a * x)) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
        rw [Real.mul_rpow (inv_nonneg.mpr ha.le) (Real.exp_nonneg _)]
        rw [← Real.rpow_neg_eq_inv_rpow]
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        ring_nf
  calc
    (x + 1) ^ B * Real.exp (-r * x) ≤
        ((2 : ℝ) ^ B * a ^ (-B) * Real.exp (B * (a * x))) *
          Real.exp (-r * x) :=
      mul_le_mul_of_nonneg_right hpow' (Real.exp_nonneg _)
    _ = (2 : ℝ) ^ B * a ^ (-B) * Real.exp (-(zeta * r) * x) := by
      have hexp :
          Real.exp (B * (a * x)) * Real.exp (-r * x) =
            Real.exp (-(zeta * r) * x) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [a]
        field_simp [hB.ne']
        ring
      rw [show
        (2 : ℝ) ^ B * a ^ (-B) * Real.exp (B * (a * x)) * Real.exp (-r * x) =
          ((2 : ℝ) ^ B * a ^ (-B)) *
            (Real.exp (B * (a * x)) * Real.exp (-r * x)) by ring]
      rw [hexp]
    _ = _ := by rfl
end CollatzEndpointTransport.FixedTotal
