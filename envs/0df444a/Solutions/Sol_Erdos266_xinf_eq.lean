-- Prove2me | solution 1 for Erdos266.xinf_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:09:28.340523+00:00
-- url     : https://prove2.me/submissions/dedbd6ea-135e-471a-89e9-50965d1390f2

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_run_target_stable
public import Theorems.Thm_Erdos266_le_dOf
public import Theorems.Thm_Erdos266_two_le_mseq


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {k i : ℕ} (hk : mseq (i + 1) ≤ k) : (run k).2 i = xinf i := by
  have h1 : i < dOf (mseq (i + 1)) :=
    lt_of_lt_of_le (Nat.lt_succ_self i) (le_dOf le_rfl)
  exact run_target_stable (two_le_mseq _) hk h1
end Erdos266
