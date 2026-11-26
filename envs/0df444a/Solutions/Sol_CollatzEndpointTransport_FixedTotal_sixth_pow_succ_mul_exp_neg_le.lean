-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sixth_pow_succ_mul_exp_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:40:02.83605+00:00
-- url     : https://prove2.me/submissions/d9d7308e-177f-4d3d-9563-72668192d5ef

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
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
    {r zeta x : ℝ}
    (hr : 0 < r) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hx : 1 ≤ x) :
    (x + 1) ^ 6 * Real.exp (-r * x) ≤
      64 * ((((1 - zeta) * r / 6)⁻¹) ^ 6) *
        Real.exp (-(zeta * r) * x) := by
  let a := (1 - zeta) * r / 6
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (mul_pos (sub_pos.mpr hzeta1) hr) (by norm_num)
  have hax : a * x ≤ Real.exp (a * x) := by
    nlinarith [Real.add_one_le_exp (a * x)]
  have hxexp : x ≤ a⁻¹ * Real.exp (a * x) := by
    calc
      x = a⁻¹ * (a * x) := by field_simp [ha.ne']
      _ ≤ a⁻¹ * Real.exp (a * x) :=
        mul_le_mul_of_nonneg_left hax (inv_nonneg.mpr ha.le)
  have hsucc : x + 1 ≤ 2 * x := by linarith
  have hpow :
      (x + 1) ^ 6 ≤
        64 * (a⁻¹) ^ 6 * Real.exp (6 * (a * x)) := by
    calc
      (x + 1) ^ 6 ≤ (2 * x) ^ 6 := by
        exact pow_le_pow_left₀ (by positivity) hsucc 6
      _ = 64 * x ^ 6 := by ring
      _ ≤ 64 * (a⁻¹ * Real.exp (a * x)) ^ 6 := by
        gcongr
      _ = 64 * (a⁻¹) ^ 6 * Real.exp (6 * (a * x)) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        ring
  calc
    (x + 1) ^ 6 * Real.exp (-r * x) ≤
        (64 * (a⁻¹) ^ 6 * Real.exp (6 * (a * x))) *
          Real.exp (-r * x) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ = 64 * (a⁻¹) ^ 6 * Real.exp (-(zeta * r) * x) := by
      rw [show
        64 * (a⁻¹) ^ 6 * Real.exp (6 * (a * x)) * Real.exp (-r * x) =
          64 * (a⁻¹) ^ 6 *
            (Real.exp (6 * (a * x)) * Real.exp (-r * x)) by ring]
      rw [← Real.exp_add]
      congr 2
      dsimp [a]
      ring
    _ = _ := by rfl
end CollatzEndpointTransport.FixedTotal
