-- Prove2me | solution 1 for Erdos266.run_target_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:08:20.897467+00:00
-- url     : https://prove2.me/submissions/9e43ab6a-d7d8-4d57-8087-af2ce4b45fa8

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_stepSt_snd_apply
public import Theorems.Thm_Erdos266_dOf_mono
public import Theorems.Thm_Erdos266_inv_run
public import Theorems.Thm_Erdos266_run_succ


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {k k' : ℕ} (h2 : 2 ≤ k) (hkk : k ≤ k') {i : ℕ} (hi : i < dOf k) :
    (run k').2 i = (run k).2 i := by
  induction k', hkk using Nat.le_induction with
  | base => rfl
  | succ k' hk' ih =>
    have hik' : i < dOf k' := lt_of_lt_of_le hi (dOf_mono hk')
    rw [run_succ (by omega), stepSt_snd_apply (inv_run k' (by omega)) hik']
    exact ih
end Erdos266
