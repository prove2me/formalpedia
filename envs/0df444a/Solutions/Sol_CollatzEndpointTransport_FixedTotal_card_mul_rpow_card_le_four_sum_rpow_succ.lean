-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_mul_rpow_card_le_four_sum_rpow_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:40:48.486299+00:00
-- url     : https://prove2.me/submissions/1d7de4e9-b88f-4cd4-90ba-e459bedca97c

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_half_card_le_card_filter_half
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
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
    (S : Finset ℕ) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1) :
    (S.card : ℝ) * (S.card : ℝ) ^ theta ≤
      4 * ∑ q ∈ S, ((q + 1 : ℕ) : ℝ) ^ theta := by
  let h := S.card / 2
  let high := S.filter fun q => h ≤ q
  have hhigh : S.card - S.card / 2 ≤ high.card := by
    simpa [h, high] using half_card_le_card_filter_half S
  have hcard : S.card ≤ 2 * high.card := by omega
  have hscale : S.card ≤ 2 * (h + 1) := by
    dsimp [h]
    omega
  have hscaleR : (S.card : ℝ) ≤ 2 * (h + 1) := by
    exact_mod_cast hscale
  have hpowTwo : (2 : ℝ) ^ theta ≤ 2 := by
    simpa using
      (Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) htheta1)
  have hpow : (S.card : ℝ) ^ theta ≤
      2 * ((h + 1 : ℕ) : ℝ) ^ theta := by
    have hmono :=
      Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ S.card)
        hscaleR htheta0.le
    calc
      (S.card : ℝ) ^ theta
          ≤ (2 * ((h + 1 : ℕ) : ℝ)) ^ theta := by
            convert hmono using 1 <;> norm_num
      _ = (2 : ℝ) ^ theta * ((h + 1 : ℕ) : ℝ) ^ theta := by
        rw [Real.mul_rpow] <;> positivity
      _ ≤ 2 * ((h + 1 : ℕ) : ℝ) ^ theta :=
        mul_le_mul_of_nonneg_right hpowTwo
          (Real.rpow_nonneg (by positivity) _)
  have hcardR : (S.card : ℝ) ≤ 2 * high.card := by
    exact_mod_cast hcard
  have hprod :
      (S.card : ℝ) * (S.card : ℝ) ^ theta ≤
        4 * (high.card : ℝ) * ((h + 1 : ℕ) : ℝ) ^ theta := by
    calc
      (S.card : ℝ) * (S.card : ℝ) ^ theta
          ≤ (2 * high.card : ℝ) * (S.card : ℝ) ^ theta :=
        mul_le_mul_of_nonneg_right hcardR
          (Real.rpow_nonneg (by positivity) _)
      _ ≤ (2 * high.card : ℝ) *
          (2 * ((h + 1 : ℕ) : ℝ) ^ theta) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 4 * (high.card : ℝ) * ((h + 1 : ℕ) : ℝ) ^ theta := by
        ring
  have hsumHigh :
      (high.card : ℝ) * ((h + 1 : ℕ) : ℝ) ^ theta ≤
        ∑ q ∈ high, ((q + 1 : ℕ) : ℝ) ^ theta := by
    calc
      (high.card : ℝ) * ((h + 1 : ℕ) : ℝ) ^ theta =
          ∑ _q ∈ high, ((h + 1 : ℕ) : ℝ) ^ theta := by simp
      _ ≤ ∑ q ∈ high, ((q + 1 : ℕ) : ℝ) ^ theta := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.rpow_le_rpow (by positivity) _ htheta0.le
        exact_mod_cast Nat.add_le_add_right (Finset.mem_filter.mp hq).2 1
  have hsumSubset :
      ∑ q ∈ high, ((q + 1 : ℕ) : ℝ) ^ theta ≤
        ∑ q ∈ S, ((q + 1 : ℕ) : ℝ) ^ theta := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _)
      (fun q _ _ => Real.rpow_nonneg (by positivity) _)
  calc
    (S.card : ℝ) * (S.card : ℝ) ^ theta
        ≤ 4 * (high.card : ℝ) * ((h + 1 : ℕ) : ℝ) ^ theta := hprod
    _ ≤ 4 * ∑ q ∈ high, ((q + 1 : ℕ) : ℝ) ^ theta := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hsumHigh (by norm_num : (0 : ℝ) ≤ 4)
    _ ≤ 4 * ∑ q ∈ S, ((q + 1 : ℕ) : ℝ) ^ theta :=
      mul_le_mul_of_nonneg_left hsumSubset (by norm_num)
end CollatzEndpointTransport.FixedTotal
