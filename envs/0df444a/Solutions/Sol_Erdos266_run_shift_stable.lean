-- Prove2me | solution 1 for Erdos266.run_shift_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:08:19.866482+00:00
-- url     : https://prove2.me/submissions/47c829b7-ca5f-4c0b-804a-933079ddc1b5

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_stepSt_fst_apply
public import Theorems.Thm_Erdos266_inv_run
public import Theorems.Thm_Erdos266_run_succ


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {k k' : ℕ} (h2 : 2 ≤ k) (hkk : k ≤ k') {l : ℕ} (hl : l < k) (j : ℕ) :
    (run k').1 l j = (run k).1 l j := by
  induction k', hkk using Nat.le_induction with
  | base => rfl
  | succ k' hk' ih =>
    rw [run_succ (by omega), stepSt_fst_apply (inv_run k' (by omega)) (by omega) j]
    exact ih
end Erdos266
