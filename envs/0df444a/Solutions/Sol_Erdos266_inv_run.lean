-- Prove2me | solution 1 for Erdos266.inv_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:07:22.870605+00:00
-- url     : https://prove2.me/submissions/b6eec42c-9b46-418f-9ddd-b78bf4a9a85d

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
public import Theorems.Thm_Erdos266_run_succ
public import Theorems.Thm_Erdos266_inv_init
public import Theorems.Thm_Erdos266_inv_step

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution (k : ℕ) (hk : 2 ≤ k) : Inv k (run k) := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h2 : run 2 = initSt := by
      rw [run, if_pos (by norm_num)]
    rw [h2]
    exact inv_init
  | succ k hk ih =>
    rw [run_succ hk]
    exact inv_step ih
end Erdos266
