-- Prove2me | solution 1 for BooleanIsoperimetry.cascadeSlice0Value_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:29.794797+00:00
-- url     : https://prove2.me/submissions/5faedea0-08bd-47a4-84dd-5c7ff6deed86

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_le_two_pow
public import Theorems.Thm_BooleanIsoperimetry_choose_succ_dim

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k r t : ℕ} (h : IsBinomialCascade (n + 1) k r t) :
    cascadeSlice0Value n r t ≤ 2 ^ n := by
  obtain ⟨_, ht, _, _⟩ := h
  have hd := choose_succ_dim n r
  have hsucc := binomPrefix_succ n r
  have hle := binomPrefix_le_two_pow n (r + 1)
  unfold cascadeSlice0Value
  omega
end BooleanIsoperimetry
