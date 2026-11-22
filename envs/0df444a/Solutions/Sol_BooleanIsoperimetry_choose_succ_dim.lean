-- Prove2me | solution 1 for BooleanIsoperimetry.choose_succ_dim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:31.298798+00:00
-- url     : https://prove2.me/submissions/692249ff-d03e-415b-86ea-f1cd351c2c25

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n r : ℕ) :
    Nat.choose (n + 1) r = Nat.choose n r + choosePred n r := by
  rcases r with _ | r
  · simp [choosePred]
  · simp [choosePred, Nat.choose_succ_succ, Nat.add_comm]
end BooleanIsoperimetry
