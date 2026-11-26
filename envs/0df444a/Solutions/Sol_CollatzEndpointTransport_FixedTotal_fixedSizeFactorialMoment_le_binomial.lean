-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedSizeFactorialMoment_le_binomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:39.455961+00:00
-- url     : https://prove2.me/submissions/14e6c524-2a53-4ef9-ab90-1971b7fe9c0e

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_choose_sub_div_choose_le_pow_div
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
variable {α : Type*} [DecidableEq α]
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {n k m : ℕ} {t : ℝ}
    (hn : 0 < n) (hkn : k ≤ n) (ht : 0 ≤ t) :
    (∑ j ∈ range (m + 1),
        if hjk : j ≤ k then
          (m.choose j : ℝ) *
            (((n - j).choose (k - j) : ℕ) : ℝ) /
              (n.choose k : ℕ) * t ^ j
        else 0) ≤
      (1 + ((k : ℝ) / n) * t) ^ m := by
  have hp : 0 ≤ (k : ℝ) / n := by positivity
  have hsum :
      (1 + ((k : ℝ) / n) * t) ^ m =
        ∑ j ∈ range (m + 1),
          (((k : ℝ) / n) * t) ^ j *
            1 ^ (m - j) * (m.choose j : ℝ) := by
    simpa [add_comm] using
      (add_pow (((k : ℝ) / n) * t) 1 m)
  rw [hsum]
  apply sum_le_sum
  intro j hj
  split_ifs with hjk
  · have hratio :=
      choose_sub_div_choose_le_pow_div hn hkn hjk
    calc
      (m.choose j : ℝ) *
            (((n - j).choose (k - j) : ℕ) : ℝ) /
              (n.choose k : ℕ) * t ^ j =
          (m.choose j : ℝ) *
            ((((n - j).choose (k - j) : ℕ) : ℝ) /
              (n.choose k : ℕ)) * t ^ j := by ring
      _ ≤ (m.choose j : ℝ) * (((k : ℝ) / n) ^ j) * t ^ j := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _))
          (pow_nonneg ht j)
      _ = ((((k : ℝ) / n) * t) ^ j) *
            1 ^ (m - j) * (m.choose j : ℝ) := by
        rw [mul_pow]
        simp
        ring
  · positivity
end CollatzEndpointTransport.FixedTotal
