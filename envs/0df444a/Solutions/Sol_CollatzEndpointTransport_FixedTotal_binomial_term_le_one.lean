-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.binomial_term_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:07.092676+00:00
-- url     : https://prove2.me/submissions/01c0b047-04be-4f74-ba6d-92c4e35b0bd4

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
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
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {n k : ℕ} {p q : ℝ}
    (hk : k ≤ n) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    (n.choose k : ℝ) * p ^ k * q ^ (n - k) ≤ 1 := by
  have hbin :
      (p + q) ^ n =
        ∑ j ∈ range (n + 1),
          p ^ j * q ^ (n - j) * (n.choose j : ℝ) :=
    add_pow p q n
  have hmem : k ∈ range (n + 1) := mem_range.mpr (Nat.lt_succ_of_le hk)
  calc
    (n.choose k : ℝ) * p ^ k * q ^ (n - k) =
        p ^ k * q ^ (n - k) * (n.choose k : ℝ) := by ring
    _ ≤ ∑ j ∈ range (n + 1),
        p ^ j * q ^ (n - j) * (n.choose j : ℝ) := by
          exact single_le_sum
            (s := range (n + 1))
            (f := fun j => p ^ j * q ^ (n - j) * (n.choose j : ℝ))
            (fun j hj => by positivity) hmem
    _ = (p + q) ^ n := hbin.symm
    _ = 1 := by simp [hpq]
end CollatzEndpointTransport.FixedTotal
