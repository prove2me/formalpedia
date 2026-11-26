-- Prove2me | solution 1 for Erdos266.Sinf_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:08:18.540938+00:00
-- url     : https://prove2.me/submissions/bce02699-23f8-4d2e-85b7-dd9317c9ac24

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_two_le_of_dOf_pos
public import Theorems.Thm_Erdos266_inv_run


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {l j : ℕ} (hj : j < dOf l) : |Sinf l j| ≤ (bigM l : ℤ) := by
  have h2 : 2 ≤ l := two_le_of_dOf_pos (by omega)
  exact (inv_run (l + 1) (by omega)).2.1 l (Nat.lt_succ_self l) j hj
end Erdos266
