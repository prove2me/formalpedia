-- Prove2me | solution 1 for Erdos266.elemZ_lt_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:09:18.469261+00:00
-- url     : https://prove2.me/submissions/43150a56-9b15-40bd-94c8-3f7a576ebb1b

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_two_le_of_dOf_pos
public import Theorems.Thm_Erdos266_Sinf_bound
public import Theorems.Thm_Erdos266_two_mul_bigM_lt


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {l j : ℕ} (hj : j + 1 < dOf l) : elemZ l j < elemZ l (j + 1) := by
  have h2 : 2 ≤ l := two_le_of_dOf_pos (by omega)
  have h3 : 2 * (bigM l : ℤ) < (bigN l : ℤ) := by exact_mod_cast two_mul_bigM_lt h2
  have hb1 := (abs_le.mp (Sinf_bound (by omega : j < dOf l))).1
  have hb2 := (abs_le.mp (Sinf_bound hj)).1
  have hb3 := (abs_le.mp (Sinf_bound (by omega : j < dOf l))).2
  have hb4 := (abs_le.mp (Sinf_bound hj)).2
  rw [elemZ, elemZ]
  have e1 : (((j + 1 + 1) * bigN l : ℕ) : ℤ) = ((j + 1) * bigN l : ℕ) + (bigN l : ℤ) := by
    push_cast
    ring
  rw [e1]
  omega
end Erdos266
