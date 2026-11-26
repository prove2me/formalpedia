-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedCriticalNumerator_div_level_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:28:07.860686+00:00
-- url     : https://prove2.me/submissions/c1237d75-7ad6-4fb5-871f-d4c5a3bac9e7

import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedCriticalNumerator_eq_zero_of_card_eq_zero
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedCriticalNumerator_nonneg
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
    (M s : ℕ) (u : Fin M)
    (hlevel : 0 < levelSourceCard M s) :
    fixedCriticalNumerator (M - (u : ℕ)) s /
        Real.sqrt (levelSourceCard M s) ≤
      fixedCriticalContribution (M - (u : ℕ)) s := by
  let W := fixedSet (M - (u : ℕ)) s
  have hWle : W.card ≤ levelSourceCard M s := by
    exact Finset.single_le_sum
      (fun i _ => Nat.zero_le (levelCohortSet M s i).card)
      (Finset.mem_univ u)
  by_cases hWzero : W.card = 0
  · have hnum :
        fixedCriticalNumerator (M - (u : ℕ)) s = 0 :=
      fixedCriticalNumerator_eq_zero_of_card_eq_zero hWzero
    simp [hnum, fixedCriticalContribution]
  · have hsqrtW : 0 < Real.sqrt W.card := by
      apply Real.sqrt_pos.mpr
      exact_mod_cast Nat.pos_of_ne_zero hWzero
    have hsqrtLevel : 0 < Real.sqrt (levelSourceCard M s) := by
      exact Real.sqrt_pos.mpr (by exact_mod_cast hlevel)
    have hsqrtLe :
        Real.sqrt W.card ≤ Real.sqrt (levelSourceCard M s) := by
      exact Real.sqrt_le_sqrt (by exact_mod_cast hWle)
    unfold fixedCriticalContribution
    exact div_le_div_of_nonneg_left
      (fixedCriticalNumerator_nonneg _ _)
      hsqrtW hsqrtLe
end CollatzEndpointTransport.FixedTotal
