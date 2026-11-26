-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.central_fixed_total_aggregate_le_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:50.72142+00:00
-- url     : https://prove2.me/submissions/f1d580e9-f1b7-4b47-a6d6-4575652a0e91

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_mul_fixedRenyiMoment_le_sharp
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_rpow_one_sub_le_card_rpow
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fixedSourceWeight_centralLengthSet_le_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralMomentConstant_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_nonneg
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
    {N : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (hN : 3 < N)
    (hsizePi :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1))
    (hsizeDrift :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N)
    (hinterior :
      ∀ s ∈ centralLengthSet N eta, 1 < s ∧ s < N) :
    (∑ s ∈ centralLengthSet N eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
      centralMomentConstant theta eta * (N + 1 : ℝ) ^ (1 + theta) := by
  classical
  let U := centralLengthSet N eta
  let K := centralMomentConstant theta eta
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact (centralMomentConstant_pos
      htheta0 htheta1 heta0 heta1).le
  have hlevel : ∀ s ∈ U,
      fixedSourceWeight N s * fixedRenyiMoment N s theta ≤
        K * (N + 1 : ℝ) *
          (fixedSourceWeight N s) ^ (1 - theta) := by
    intro s hs
    have hsData := hinterior s hs
    have hsMem :
        s ∈ Finset.Icc 1 N ∧ InCentralRenyiWindow N s eta := by
      simpa [U, centralLengthSet] using hs
    exact fixedSourceWeight_mul_fixedRenyiMoment_le_sharp
      htheta0 htheta1 heta0 heta1 (by omega)
      hsData.1 hsData.2 hsMem.2 hsizePi hsizeDrift
  have hpowers :
      ∑ s ∈ U, (fixedSourceWeight N s) ^ (1 - theta) ≤
        (U.card : ℝ) ^ theta := by
    exact sum_rpow_one_sub_le_card_rpow U
      (fun s => fixedSourceWeight N s)
      htheta0 htheta1
      (fun s hs => fixedSourceWeight_nonneg N s)
      (by simpa [U] using
        sum_fixedSourceWeight_centralLengthSet_le_one (by omega : 0 < N) eta)
  have hcard : (U.card : ℝ) ≤ (N + 1 : ℝ) := by
    have hsub : U ⊆ Finset.range (N + 1) := by
      intro s hs
      have hsIcc : s ∈ Finset.Icc 1 N := by
        exact (Finset.mem_filter.mp hs).1
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.mem_Icc.mp hsIcc).2)
    have hc := Finset.card_le_card hsub
    simpa using (show (U.card : ℝ) ≤ ((Finset.range (N + 1)).card : ℝ) by
      exact_mod_cast hc)
  have hcardPow : (U.card : ℝ) ^ theta ≤ (N + 1 : ℝ) ^ theta :=
    Real.rpow_le_rpow (by positivity) hcard htheta0.le
  calc
    (∑ s ∈ centralLengthSet N eta,
        fixedSourceWeight N s * fixedRenyiMoment N s theta) ≤
        ∑ s ∈ U,
          K * (N + 1 : ℝ) *
            (fixedSourceWeight N s) ^ (1 - theta) := by
      simpa [U] using Finset.sum_le_sum hlevel
    _ = K * (N + 1 : ℝ) *
          ∑ s ∈ U, (fixedSourceWeight N s) ^ (1 - theta) := by
      rw [Finset.mul_sum]
    _ ≤ K * (N + 1 : ℝ) * (U.card : ℝ) ^ theta := by
      exact mul_le_mul_of_nonneg_left hpowers
        (mul_nonneg hK0 (by positivity))
    _ ≤ K * (N + 1 : ℝ) * (N + 1 : ℝ) ^ theta := by
      exact mul_le_mul_of_nonneg_left hcardPow
        (mul_nonneg hK0 (by positivity))
    _ = centralMomentConstant theta eta *
          (N + 1 : ℝ) ^ (1 + theta) := by
      dsimp [K]
      rw [Real.rpow_add (by positivity : (0 : ℝ) < N + 1)]
      rw [Real.rpow_one]
      ring
end CollatzEndpointTransport.FixedTotal
