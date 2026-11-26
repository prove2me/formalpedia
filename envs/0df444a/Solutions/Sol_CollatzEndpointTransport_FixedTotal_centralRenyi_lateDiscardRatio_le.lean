-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyi_lateDiscardRatio_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:39:38.57577+00:00
-- url     : https://prove2.me/submissions/0bec702b-fa02-450b-b048-9a1584032f66

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyi_lateDiscardRatio_eq
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
    (eta : ℝ) (M : ℕ)
    (hKM : centralRenyiDiscardDepth eta M ≤ M) :
    (((((M + 1) *
        2 ^ (M - centralRenyiDiscardDepth eta M) : ℕ) : ℝ) /
        (2 ^ M : ℝ))) ≤
      2 * (M + 1 : ℝ) *
        Real.exp (-(eta * Real.log 2 / 8) * M) := by
  let K := centralRenyiDiscardDepth eta M
  rw [centralRenyi_lateDiscardRatio_eq hKM]
  have hfloor := Nat.lt_floor_add_one (eta * (M : ℝ) / 8)
  have hKlower : eta * (M : ℝ) / 8 - 1 < K := by
    dsimp [K, centralRenyiDiscardDepth]
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp :
      Real.exp (-(Real.log 2) * K) ≤
        2 * Real.exp (-(eta * Real.log 2 / 8) * M) := by
    have hmono :
        -(Real.log 2) * K ≤
          -(Real.log 2) * (eta * (M : ℝ) / 8 - 1) := by
      nlinarith
    have hid :
        Real.exp (-(Real.log 2) * (eta * (M : ℝ) / 8 - 1)) =
          2 * Real.exp (-(eta * Real.log 2 / 8) * M) := by
      rw [show
        -(Real.log 2) * (eta * (M : ℝ) / 8 - 1) =
          Real.log 2 + (-(eta * Real.log 2 / 8) * M) by ring]
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [← hid]
    exact Real.exp_le_exp.mpr hmono
  calc
    (M + 1 : ℝ) * Real.exp (-(Real.log 2) * K) ≤
        (M + 1 : ℝ) *
          (2 * Real.exp (-(eta * Real.log 2 / 8) * M)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 2 * (M + 1 : ℝ) *
          Real.exp (-(eta * Real.log 2 / 8) * M) := by ring
end CollatzEndpointTransport.FixedTotal
