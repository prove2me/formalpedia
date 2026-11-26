-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_mul_sqrt_card_le_four_sum_sqrt_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:39.767834+00:00
-- url     : https://prove2.me/submissions/f623c71f-69c8-4241-aa35-30ded59de9aa

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_half_card_le_card_filter_half
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (S : Finset ℕ) :
    (S.card : ℝ) * Real.sqrt S.card ≤
      4 * ∑ q ∈ S, Real.sqrt (q + 1) := by
  let h := S.card / 2
  let high := S.filter fun q => h ≤ q
  have hhigh :
      S.card - S.card / 2 ≤ high.card := by
    simpa [h, high] using half_card_le_card_filter_half S
  have hcard : S.card ≤ 2 * high.card := by omega
  have hscale : S.card ≤ 4 * (h + 1) := by
    dsimp [h]
    omega
  have hsqrt :
      Real.sqrt S.card ≤ 2 * Real.sqrt (h + 1) := by
    have hS0 : (0 : ℝ) ≤ S.card := by positivity
    have hh0 : (0 : ℝ) ≤ h + 1 := by positivity
    have hsS := Real.sq_sqrt hS0
    have hsh := Real.sq_sqrt hh0
    have hsqrtS : 0 ≤ Real.sqrt S.card := Real.sqrt_nonneg _
    have hsqrth : 0 ≤ Real.sqrt (h + 1) := Real.sqrt_nonneg _
    have hscaleR : (S.card : ℝ) ≤ 4 * (h + 1) := by
      exact_mod_cast hscale
    nlinarith
  have hprod :
      (S.card : ℝ) * Real.sqrt S.card ≤
        4 * (high.card : ℝ) * Real.sqrt (h + 1) := by
    have hcardR : (S.card : ℝ) ≤ 2 * high.card := by
      exact_mod_cast hcard
    have hS0 : (0 : ℝ) ≤ S.card := by positivity
    have hhcard0 : (0 : ℝ) ≤ high.card := by positivity
    have hsqrtS : 0 ≤ Real.sqrt S.card := Real.sqrt_nonneg _
    have hsqrth : 0 ≤ Real.sqrt (h + 1) := Real.sqrt_nonneg _
    calc
      (S.card : ℝ) * Real.sqrt S.card
          ≤ (2 * high.card : ℝ) * Real.sqrt S.card :=
        mul_le_mul_of_nonneg_right hcardR hsqrtS
      _ ≤ (2 * high.card : ℝ) * (2 * Real.sqrt (h + 1)) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = 4 * (high.card : ℝ) * Real.sqrt (h + 1) := by ring
  have hsumHigh :
      (high.card : ℝ) * Real.sqrt (h + 1) ≤
        ∑ q ∈ high, Real.sqrt (q + 1) := by
    calc
      (high.card : ℝ) * Real.sqrt (h + 1)
          = ∑ q ∈ high, Real.sqrt (h + 1) := by simp
      _ ≤ ∑ q ∈ high, Real.sqrt (q + 1) := by
        apply Finset.sum_le_sum
        intro q hq
        have hhq : h ≤ q := (Finset.mem_filter.mp hq).2
        exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_right hhq 1)
  have hsumSubset :
      ∑ q ∈ high, Real.sqrt (q + 1) ≤
        ∑ q ∈ S, Real.sqrt (q + 1) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _)
      (fun q _ _ => Real.sqrt_nonneg _)
  calc
    (S.card : ℝ) * Real.sqrt S.card
        ≤ 4 * (high.card : ℝ) * Real.sqrt (h + 1) := hprod
    _ ≤ 4 * ∑ q ∈ high, Real.sqrt (q + 1) := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hsumHigh (by norm_num : (0 : ℝ) ≤ 4)
    _ ≤ 4 * ∑ q ∈ S, Real.sqrt (q + 1) :=
      mul_le_mul_of_nonneg_left hsumSubset (by norm_num : (0 : ℝ) ≤ 4)
end CollatzEndpointTransport.FixedTotal
