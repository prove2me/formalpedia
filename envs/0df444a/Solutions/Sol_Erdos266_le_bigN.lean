-- Prove2me | solution 1 for Erdos266.le_bigN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:01:56.697601+00:00
-- url     : https://prove2.me/submissions/9131568f-15f6-4dc1-84c6-eee1162761ba

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_succ_le_two_pow


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution (k : ℕ) : k ≤ bigN k := by
  have h4 := succ_le_two_pow k
  have h5 : (2:ℕ) ^ k ≤ bigN k := by
    rw [bigN]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_self_pow (by norm_num) k)
  omega
end Erdos266
