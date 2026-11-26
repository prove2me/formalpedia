-- Prove2me | solution 1 for Erdos266.elemZ_lb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:09:16.97463+00:00
-- url     : https://prove2.me/submissions/a80f22e6-3383-42d6-a050-5734d4a60738

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_Sinf_bound

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {l j : ℕ} (hj : j < dOf l) : (bigN l : ℤ) - bigM l ≤ elemZ l j := by
  have h1 : (bigN l : ℤ) ≤ ((j + 1) * bigN l : ℕ) := by
    exact_mod_cast Nat.le_mul_of_pos_left _ (by omega : 0 < j + 1)
  have h2 := (abs_le.mp (Sinf_bound hj)).1
  rw [elemZ]
  omega
end Erdos266
