-- Prove2me | solution 1 for Erdos266.Sinf_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:10:45.119495+00:00
-- url     : https://prove2.me/submissions/539341e9-1f0e-4985-a898-472b52c46eec

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_run_one
public import Theorems.Thm_Erdos266_run_two
public import Theorems.Thm_Erdos266_run_shift_stable

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {k l : ℕ} (h2 : 2 ≤ k) (hl : l < k) (j : ℕ) :
    (run k).1 l j = Sinf l j := by
  rcases Nat.lt_or_ge l 1 with h | h
  · have hl0 : l = 0 := by omega
    subst hl0
    have e1 : (run k).1 0 j = (run 2).1 0 j :=
      run_shift_stable le_rfl h2 (by norm_num) j
    change (run k).1 0 j = (run 1).1 0 j
    rw [e1, run_two, run_one]
  · exact run_shift_stable (by omega) (by omega) (by omega) j
end Erdos266
