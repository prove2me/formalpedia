-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedReverseSpendSum_le_hypergeometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:54.514607+00:00
-- url     : https://prove2.me/submissions/4f71d387-626f-4ab4-8dab-4e1ae3eff66d

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_hypergeometricChooseMoment_ambient_le
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
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalSpendSlice_le
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
    fixedReverseSpendSum N s theta D ≤
      ((N - 2).choose (s - 2) : ℝ) *
        (1 + (((s - 2 : ℕ) : ℝ) / (N - 2 : ℕ)) *
          ((3 : ℝ) ^ theta - 1)) ^ (D - 1) /
        (((2 : ℝ) ^ D) ^ theta) := by
  let H : ℕ → ℝ := fun j =>
    if _hjk : j ≤ s - 2 then
      ((D - 1).choose j : ℝ) *
        ((N - 2 - (D - 1)).choose (s - 2 - j) : ℝ) *
          ((3 : ℝ) ^ theta) ^ j
    else 0
  have ht0 : 0 ≤ (3 : ℝ) ^ theta - 1 := by
    linarith [Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) htheta.le]
  have hmoment :=
    hypergeometricChooseMoment_ambient_le
      (n := N - 2) (k := s - 2) (m := D - 1)
      (t := (3 : ℝ) ^ theta - 1)
      (by omega) (by omega) (by omega) ht0
  have hchoosePos : 0 < (((N - 2).choose (s - 2) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : s - 2 ≤ N - 2)
  have hambient :
      (∑ j ∈ range (N - 1), H j) ≤
        ((N - 2).choose (s - 2) : ℝ) *
          (1 + (((s - 2 : ℕ) : ℝ) / (N - 2 : ℕ)) *
            ((3 : ℝ) ^ theta - 1)) ^ (D - 1) := by
    have hraw := (div_le_iff₀ hchoosePos).mp hmoment
    simpa [H, show N - 2 + 1 = N - 1 by omega, mul_comm] using hraw
  have hsub : range (s - 1) ⊆ range (N - 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hextend :
      (∑ j ∈ range (s - 1), H j) =
        ∑ j ∈ range (N - 1), H j := by
    apply Finset.sum_subset hsub
    intro j hj hnot
    have hsj : s - 2 < j := by
      have hnotlt : ¬j < s - 1 := by
        simpa only [Finset.mem_range] using hnot
      omega
    simp [H, Nat.not_le.mpr hsj]
  have hslice :
      fixedReverseSpendSum N s theta D ≤
        (∑ j ∈ range (s - 1), H j) /
          (((2 : ℝ) ^ D) ^ theta) := by
    unfold fixedReverseSpendSum
    rw [Finset.sum_Ico_eq_sum_range]
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply sum_le_sum
    intro j hj
    have hjBound : j ≤ s - 2 := by
      exact Nat.le_pred_of_lt (Finset.mem_range.mp hj)
    have hraw := terminalSpendSlice_le
      (N := N) (s := s) (r := 1 + j) (D := D) theta
      (by omega) (by omega)
    calc
      (∑ d ∈ terminalPatternSet N s (1 + j) D,
          (terminalFiber N s (1 + j) d).card *
            realTerminalPatternTerm theta (1 + j) d) ≤
          ((D - 1).choose ((1 + j) - 1) : ℝ) *
            ((N - D - 1).choose (s - (1 + j) - 1) : ℝ) *
              realTerminalSpendTerm theta (1 + j) D := hraw
      _ = H j / (((2 : ℝ) ^ D) ^ theta) := by
        have hindexOne : 1 + j - 1 = j := by omega
        have hindexTwo : N - D - 1 = N - 2 - (D - 1) := by omega
        have hindexThree : s - (1 + j) - 1 = s - 2 - j := by omega
        simp only [H, dif_pos hjBound, realTerminalSpendTerm]
        rw [hindexOne, hindexTwo, hindexThree]
        ring
  rw [hextend] at hslice
  exact hslice.trans
    (div_le_div_of_nonneg_right hambient (by positivity))
end CollatzEndpointTransport.FixedTotal
