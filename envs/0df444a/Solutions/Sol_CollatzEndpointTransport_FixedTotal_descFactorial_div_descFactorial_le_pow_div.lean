-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.descFactorial_div_descFactorial_le_pow_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:48:34.347839+00:00
-- url     : https://prove2.me/submissions/05854139-1181-407f-8921-62e5cac36c38

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
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
    {n k j : ℕ} (hn : 0 < n) (hkn : k ≤ n) (hjk : j ≤ k) :
    ((k.descFactorial j : ℕ) : ℝ) /
        ((n.descFactorial j : ℕ) : ℝ) ≤
      ((k : ℝ) / n) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjk' : j < k := Nat.lt_of_succ_le hjk
      have hjn' : j < n := hjk'.trans_le hkn
      have hjnR : (j : ℝ) < n := by exact_mod_cast hjn'
      have hnj : 0 < (n : ℝ) - j := by linarith
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
      have hfactor :
          ((k - j : ℕ) : ℝ) / (n - j : ℕ) ≤
            (k : ℝ) / n := by
        rw [Nat.cast_sub (Nat.le_of_lt hjk'),
          Nat.cast_sub (Nat.le_of_lt hjn')]
        apply (div_le_div_iff₀ hnj hn0).2
        have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
        have hjmul : (j : ℝ) * k ≤ (j : ℝ) * n :=
          mul_le_mul_of_nonneg_left hknR (Nat.cast_nonneg j)
        calc
          ((k : ℝ) - j) * n = k * n - j * n := by ring
          _ ≤ k * n - j * k := sub_le_sub_left hjmul (k * n)
          _ = k * (n - j) := by ring
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul,
        Nat.cast_mul, pow_succ]
      rw [mul_div_mul_comm]
      simpa [mul_comm] using
        (mul_le_mul hfactor (ih (Nat.le_of_lt hjk'))
          (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (by positivity))
end CollatzEndpointTransport.FixedTotal
