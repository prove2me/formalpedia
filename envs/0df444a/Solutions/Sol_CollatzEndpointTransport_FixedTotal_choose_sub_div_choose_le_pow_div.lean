-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.choose_sub_div_choose_le_pow_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:49:22.740859+00:00
-- url     : https://prove2.me/submissions/543320b2-f428-4d04-8e9f-7a436e4aa27c

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_descFactorial_div_descFactorial_le_pow_div
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
    (((n - j).choose (k - j) : ℕ) : ℝ) / (n.choose k : ℕ) ≤
      ((k : ℝ) / n) ^ j := by
  have hjn : j ≤ n := hjk.trans hkn
  have hchooseNK : (n.choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hkn).ne'
  have hchooseNJ : (n.choose j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hjn).ne'
  have hfactorial : (j.factorial : ℝ) ≠ 0 := by positivity
  have hchoose :
      (n.choose k : ℝ) * (k.choose j : ℝ) =
        (n.choose j : ℝ) * ((n - j).choose (k - j) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := n) (k := k) hjk
  have hratioChoose :
      (((n - j).choose (k - j) : ℕ) : ℝ) / (n.choose k : ℕ) =
        (k.choose j : ℝ) / (n.choose j : ℝ) := by
    apply (div_eq_div_iff hchooseNK hchooseNJ).2
    simpa [mul_comm] using hchoose.symm
  have hkDesc :
      (k.descFactorial j : ℝ) = (j.factorial : ℝ) * (k.choose j : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose k j
  have hnDesc :
      (n.descFactorial j : ℝ) = (j.factorial : ℝ) * (n.choose j : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n j
  rw [hratioChoose]
  calc
    (k.choose j : ℝ) / (n.choose j : ℝ) =
        (k.descFactorial j : ℝ) / (n.descFactorial j : ℝ) := by
      rw [hkDesc, hnDesc]
      field_simp
    _ ≤ ((k : ℝ) / n) ^ j :=
      descFactorial_div_descFactorial_le_pow_div hn hkn hjk
end CollatzEndpointTransport.FixedTotal
