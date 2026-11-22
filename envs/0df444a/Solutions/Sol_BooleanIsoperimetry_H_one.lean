-- Prove2me | solution 1 for BooleanIsoperimetry.H_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:38.692139+00:00
-- url     : https://prove2.me/submissions/7a34388c-5d8b-4ba3-ae60-3445552024c7

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_cascadeSplit_one
public import Theorems.Thm_BooleanIsoperimetry_H_ge_self
public import Theorems.Thm_BooleanIsoperimetry_H_le_cube
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ) : H n 1 = n + 1 := by
  induction n with
  | zero =>
      have h1 : 1 ≤ H 0 1 := H_ge_self 0 1 (by norm_num)
      have h2 : H 0 1 ≤ 2 ^ 0 := H_le_cube 0 1
      omega
  | succ n ih =>
      rw [H_succ_cascade (cascadeSplit_one n), H_zero, ih]
      simp
end BooleanIsoperimetry
