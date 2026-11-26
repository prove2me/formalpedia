-- Prove2me | solution 1 for Erdos266.twice_succ_le_bigN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:04:26.485967+00:00
-- url     : https://prove2.me/submissions/359bb6ab-e2fd-4ee1-b9ba-9e3030c468ac

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_bigN_succ
public import Theorems.Thm_Erdos266_succ_le_two_pow


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution (k : ℕ) : 2 * (k + 1) * bigN k ≤ bigN (k + 1) := by
  rw [bigN_succ]
  have h4 : 2 * (k + 1) ≤ 2 ^ (2 * k + 1) := by
    have h5 := succ_le_two_pow (2 * k)
    calc 2 * (k + 1) ≤ 2 * (2 * k + 1) := by omega
    _ ≤ 2 * 2 ^ (2 * k) := by omega
    _ = 2 ^ (2 * k + 1) := by ring
  exact Nat.mul_le_mul_right _ h4
end Erdos266
