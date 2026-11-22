-- Prove2me | solution 1 for BooleanIsoperimetry.binomPrefix_pred_add_choosePred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:16:27.673108+00:00
-- url     : https://prove2.me/submissions/3eff893f-917e-4537-a1ff-041a37b2177d

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_zero
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n r : ℕ) :
    binomPrefix n (r - 1) + choosePred n r = binomPrefix n r := by
  rcases r with _ | r
  · simp [choosePred, binomPrefix_zero]
  · simp only [Nat.add_sub_cancel, choosePred, Nat.succ_ne_zero, ite_false,
      Nat.add_sub_cancel]
    rw [binomPrefix_succ]
end BooleanIsoperimetry
