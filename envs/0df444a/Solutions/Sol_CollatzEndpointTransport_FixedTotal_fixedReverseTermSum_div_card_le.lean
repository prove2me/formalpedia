-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedReverseTermSum_div_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:47:43.967215+00:00
-- url     : https://prove2.me/submissions/61f2115a-2bcd-43f8-8f59-25b6aa4c978b

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_realTerminalSpendTerm_nonneg
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseTermSum_eq_spend
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalSpendSlice_div_card_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_summable_terminal_majorant
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_tsum_terminal_majorant
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPatternSet_eq_empty_of_spend_lt
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne


attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.normalizedReverseLift_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s r : ℕ} {theta : ℝ}
    (htheta : 0 < theta)
    (hN : 1 < N) (hs1 : 1 < s) (hsN : s < N)
    (hr0 : 0 < r) (hrs : r < s) :
    fixedReverseTermSum N s theta r / ((fixedSet N s).card : ℝ) ≤
      (N : ℝ) * (3 : ℝ) ^ (-theta) *
        centralRenyiRatio theta (centralSeparatorProportion N s) ^ r := by
  let pi := centralSeparatorProportion N s
  let g : ℕ → ℝ := fun n =>
    pi ^ r * (1 - pi) ^ n *
      ((n + r - 1).choose (r - 1) : ℝ) *
      realTerminalSpendTerm theta r (n + r)
  have hpi0 : 0 ≤ pi := by
    dsimp [pi, centralSeparatorProportion]
    positivity
  have hpi1 : pi ≤ 1 := by
    dsimp [pi, centralSeparatorProportion]
    have hNm1 : 0 < (N - 1 : ℕ) := by omega
    apply (div_le_one (by exact_mod_cast hNm1 : (0 : ℝ) < (N - 1 : ℕ))).2
    exact_mod_cast (by omega : s - 1 ≤ N - 1)
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    dsimp [g]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg hpi0 _) (pow_nonneg (sub_nonneg.mpr hpi1) _))
        (Nat.cast_nonneg _))
      (realTerminalSpendTerm_nonneg theta r (n + r))
  have hgsum : Summable g := by
    simpa [g] using
      (summable_terminal_majorant
        (theta := theta) (pi := pi) (r := r) htheta hpi0 hpi1 hr0)
  rw [fixedReverseTermSum_eq_spend, div_eq_mul_inv, Finset.sum_mul]
  calc
    (∑ D ∈ range (N + 1),
        (∑ d ∈ terminalPatternSet N s r D,
          (terminalFiber N s r d).card *
            realTerminalPatternTerm theta r d) /
              ((fixedSet N s).card : ℝ)) ≤
        ∑ D ∈ range (N + 1),
          if r ≤ D then (N : ℝ) * g (D - r) else 0 := by
      apply sum_le_sum
      intro D hD
      by_cases hrD : r ≤ D
      · rw [if_pos hrD]
        have hslice := terminalSpendSlice_div_card_le
          (N := N) (s := s) (r := r) (D := D) theta
          hN hs1 hsN hr0 hrs
        calc
          (∑ d ∈ terminalPatternSet N s r D,
              (terminalFiber N s r d).card *
                realTerminalPatternTerm theta r d) /
                ((fixedSet N s).card : ℝ) ≤
              (N : ℝ) * centralSeparatorProportion N s ^ r *
                (1 - centralSeparatorProportion N s) ^ (D - r) *
                ((D - 1).choose (r - 1) : ℝ) *
                realTerminalSpendTerm theta r D := hslice
          _ = (N : ℝ) * g (D - r) := by
            simp only [g, pi, Nat.sub_add_cancel hrD]
            ring
      · have hDr : D < r := Nat.lt_of_not_ge hrD
        have hempty := terminalPatternSet_eq_empty_of_spend_lt
          (N := N) hrs.le hDr
        rw [hempty, if_neg hrD]
        simp
    _ = ∑ D ∈ Ico r (N + 1), (N : ℝ) * g (D - r) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext D
        simp [and_comm]
      · intro D hD
        rfl
    _ = ∑ n ∈ range (N + 1 - r), (N : ℝ) * g n := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply sum_congr rfl
      intro n hn
      rw [Nat.add_sub_cancel_left]
    _ ≤ (N : ℝ) * ∑' n : ℕ, g n := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (hgsum.sum_le_tsum (range (N + 1 - r))
          (fun n _ => hg0 n))
        (Nat.cast_nonneg N)
    _ = (N : ℝ) * (3 : ℝ) ^ (-theta) *
        centralRenyiRatio theta (centralSeparatorProportion N s) ^ r := by
      have htsum := tsum_terminal_majorant
        (theta := theta) (pi := pi) (r := r)
        htheta hpi0 hpi1 hr0
      rw [htsum]
      simp only [pi]
      ring
end CollatzEndpointTransport.FixedTotal
