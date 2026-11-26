-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedReverseSpendSum_div_card_le_fixedSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:42.85718+00:00
-- url     : https://prove2.me/submissions/5f5f7f82-67c3-4c2d-bb61-4e12bc266168

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseSpendSum_le_hypergeometric
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_choose_two_sub_div_fixedSet_eq_separator
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_conditionalSeparatorProportion_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
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
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
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



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s D : ℕ} {theta : ℝ}
    (htheta : 0 < theta)
    (hN : 2 < N) (hs1 : 1 < s) (hsN : s < N)
    (hD0 : 0 < D) (hDN : D < N) :
    fixedReverseSpendSum N s theta D /
        ((fixedSet N s).card : ℝ) ≤
      centralSeparatorProportion N s *
        (1 + centralSeparatorProportion N s *
          ((3 : ℝ) ^ theta - 1)) ^ (D - 1) /
        (((2 : ℝ) ^ D) ^ theta) := by
  have hcard : 0 < ((fixedSet N s).card : ℝ) := by
    rw [card_fixedSet N s (by omega) (by omega)]
    exact_mod_cast Nat.choose_pos (by omega : s - 1 ≤ N - 1)
  have hbase := fixedReverseSpendSum_le_hypergeometric
    htheta hN hs1 hsN hD0 hDN
  have ht0 : 0 ≤ (3 : ℝ) ^ theta - 1 := by
    linarith [Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) htheta.le]
  have hpi0 : 0 ≤ centralSeparatorProportion N s := by
    unfold centralSeparatorProportion
    positivity
  have hconditional := conditionalSeparatorProportion_le hN hs1 hsN
  have hinside :
      1 + (((s - 2 : ℕ) : ℝ) / (N - 2 : ℕ)) *
          ((3 : ℝ) ^ theta - 1) ≤
        1 + centralSeparatorProportion N s *
          ((3 : ℝ) ^ theta - 1) := by
    simpa [add_comm] using
      (add_le_add_left
        (mul_le_mul_of_nonneg_right hconditional ht0) 1)
  have hpow :
      (1 + (((s - 2 : ℕ) : ℝ) / (N - 2 : ℕ)) *
          ((3 : ℝ) ^ theta - 1)) ^ (D - 1) ≤
        (1 + centralSeparatorProportion N s *
          ((3 : ℝ) ^ theta - 1)) ^ (D - 1) :=
    pow_le_pow_left₀ (by positivity) hinside (D - 1)
  have hratio :=
    choose_two_sub_div_fixedSet_eq_separator hN hs1 hsN
  calc
    fixedReverseSpendSum N s theta D /
          ((fixedSet N s).card : ℝ) ≤
        (((N - 2).choose (s - 2) : ℕ) : ℝ) *
          (1 + (((s - 2 : ℕ) : ℝ) / (N - 2 : ℕ)) *
            ((3 : ℝ) ^ theta - 1)) ^ (D - 1) /
          (((2 : ℝ) ^ D) ^ theta) /
          ((fixedSet N s).card : ℝ) := by
      exact div_le_div_of_nonneg_right hbase hcard.le
    _ = centralSeparatorProportion N s *
          (1 + (((s - 2 : ℕ) : ℝ) / (N - 2 : ℕ)) *
            ((3 : ℝ) ^ theta - 1)) ^ (D - 1) /
          (((2 : ℝ) ^ D) ^ theta) := by
      rw [← hratio]
      ring
    _ ≤ centralSeparatorProportion N s *
          (1 + centralSeparatorProportion N s *
            ((3 : ℝ) ^ theta - 1)) ^ (D - 1) /
          (((2 : ℝ) ^ D) ^ theta) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hpi0) (by positivity)
end CollatzEndpointTransport.FixedTotal
