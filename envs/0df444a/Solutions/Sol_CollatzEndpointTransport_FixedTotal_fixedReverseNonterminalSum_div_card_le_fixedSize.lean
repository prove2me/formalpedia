-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedReverseNonterminalSum_div_card_le_fixedSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:46:45.341926+00:00
-- url     : https://prove2.me/submissions/2773530a-a4c2-4038-9521-d1e64d429f4b

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseSpendSum_div_card_le_fixedSize
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSizeReverseRatio_nonneg
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSizeReverseRatio_lt_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseNonterminalSum_eq_sum_spend
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseSpendSum_zero
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseSpendSum_total
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAlpha_den_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_natPow_rpow_eq_rpow_natPow
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
    {N s : ℕ} {theta : ℝ}
    (htheta : 0 < theta)
    (hN : 2 < N) (hs1 : 1 < s) (hsN : s < N)
    (hpiAlpha :
      centralSeparatorProportion N s < centralRenyiAlpha theta) :
    fixedReverseNonterminalSum N s theta /
        ((fixedSet N s).card : ℝ) ≤
      centralSeparatorProportion N s /
        ((2 : ℝ) ^ theta - 1 -
          centralSeparatorProportion N s * ((3 : ℝ) ^ theta - 1)) := by
  let pi := centralSeparatorProportion N s
  let Q := fixedSizeReverseRatio theta pi
  have hpi0 : 0 < pi := by
    dsimp [pi, centralSeparatorProportion]
    exact div_pos
      (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hs1))
      (Nat.cast_pos.mpr (Nat.sub_pos_of_lt (by omega : 1 < N)))
  have hQ0 : 0 ≤ Q := fixedSizeReverseRatio_nonneg htheta hpi0.le
  have hQ1 : Q < 1 := fixedSizeReverseRatio_lt_one htheta hpiAlpha
  have hsummable : Summable fun j : ℕ =>
      pi / (2 : ℝ) ^ theta * Q ^ j :=
    (summable_geometric_of_lt_one hQ0 hQ1).mul_left
      (pi / (2 : ℝ) ^ theta)
  rw [fixedReverseNonterminalSum_eq_sum_spend,
    div_eq_mul_inv, Finset.sum_mul]
  calc
    (∑ D ∈ range (N + 1),
        fixedReverseSpendSum N s theta D /
          ((fixedSet N s).card : ℝ)) ≤
        ∑ D ∈ range (N + 1),
          if 0 < D ∧ D < N then
            pi * (1 + pi * ((3 : ℝ) ^ theta - 1)) ^ (D - 1) /
              (((2 : ℝ) ^ D) ^ theta)
          else 0 := by
      apply sum_le_sum
      intro D hD
      by_cases hvalid : 0 < D ∧ D < N
      · rw [if_pos hvalid]
        simpa [pi] using
          fixedReverseSpendSum_div_card_le_fixedSize
            htheta hN hs1 hsN hvalid.1 hvalid.2
      · rw [if_neg hvalid]
        have hDle : D ≤ N := Nat.le_of_lt_succ (mem_range.mp hD)
        rcases not_and_or.mp hvalid with hD0 | hDN
        · have hDz : D = 0 := Nat.eq_zero_of_not_pos hD0
          subst D
          simp [fixedReverseSpendSum_zero (theta := theta) (N := N)]
        · have hDeq : D = N := by omega
          subst D
          simp [fixedReverseSpendSum_total (theta := theta)]
    _ = ∑ D ∈ Ico 1 N,
          pi * (1 + pi * ((3 : ℝ) ^ theta - 1)) ^ (D - 1) /
            (((2 : ℝ) ^ D) ^ theta) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext D
        simp only [mem_filter, mem_range, mem_Ico]
        omega
      · intro D hD
        rfl
    _ = ∑ j ∈ range (N - 1),
          pi / (2 : ℝ) ^ theta * Q ^ j := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply sum_congr rfl
      intro j hj
      have htwo : 0 < (2 : ℝ) ^ theta := by positivity
      rw [natPow_rpow_eq_rpow_natPow (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [Q, fixedSizeReverseRatio]
      rw [show 1 + j - 1 = j by omega, show 1 + j = j + 1 by omega,
        pow_succ, div_pow]
      field_simp [ne_of_gt htwo]
    _ ≤ ∑' j : ℕ, pi / (2 : ℝ) ^ theta * Q ^ j := by
      exact hsummable.sum_le_tsum (range (N - 1))
        (fun j _ => by positivity)
    _ = pi /
        ((2 : ℝ) ^ theta - 1 - pi * ((3 : ℝ) ^ theta - 1)) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hQ0 hQ1]
      have htwo : 0 < (2 : ℝ) ^ theta := by positivity
      have hden : 0 < (2 : ℝ) ^ theta - 1 -
          pi * ((3 : ℝ) ^ theta - 1) := by
        have hscaled :
            pi * ((3 : ℝ) ^ theta - 1) < (2 : ℝ) ^ theta - 1 := by
          have hgap := centralRenyiAlpha_den_pos htheta
          unfold centralRenyiAlpha at hpiAlpha
          simpa [mul_comm] using (lt_div_iff₀ hgap).mp hpiAlpha
        linarith
      dsimp [Q, fixedSizeReverseRatio]
      rw [show
        1 - (1 + pi * ((3 : ℝ) ^ theta - 1)) / (2 : ℝ) ^ theta =
          ((2 : ℝ) ^ theta - 1 -
            pi * ((3 : ℝ) ^ theta - 1)) / (2 : ℝ) ^ theta by
        field_simp [ne_of_gt htwo]
        ring]
      rw [inv_div]
      field_simp [ne_of_gt htwo, ne_of_gt hden]
    _ = centralSeparatorProportion N s /
        ((2 : ℝ) ^ theta - 1 -
          centralSeparatorProportion N s * ((3 : ℝ) ^ theta - 1)) := by
      rfl
end CollatzEndpointTransport.FixedTotal
