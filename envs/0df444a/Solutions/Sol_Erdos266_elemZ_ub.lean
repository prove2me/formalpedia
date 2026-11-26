-- Prove2me | solution 1 for Erdos266.elemZ_ub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:09:17.75618+00:00
-- url     : https://prove2.me/submissions/ee52593a-a14a-418a-a0ae-e13c25580e1a

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_Sinf_bound
public import Theorems.Thm_Erdos266_dOf_le


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {l j : ℕ} (hj : j < dOf l) : elemZ l j ≤ (l * bigN l : ℤ) + bigM l := by
  have h1 : ((j + 1) * bigN l : ℕ) ≤ (l * bigN l : ℕ) := by
    have hd := dOf_le l
    exact Nat.mul_le_mul_right _ (by omega)
  have h1' : (((j + 1) * bigN l : ℕ) : ℤ) ≤ ((l * bigN l : ℕ) : ℤ) := by exact_mod_cast h1
  have h2 := (abs_le.mp (Sinf_bound hj)).2
  rw [elemZ]
  push_cast at h1' ⊢
  omega
end Erdos266
