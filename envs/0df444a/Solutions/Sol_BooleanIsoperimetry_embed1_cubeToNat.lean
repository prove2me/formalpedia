-- Prove2me | solution 1 for BooleanIsoperimetry.embed1_cubeToNat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:30.205429+00:00
-- url     : https://prove2.me/submissions/0fbde83c-9f69-47a3-89b6-1cbcac8fa5bf

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (x : Cube n) : cubeToNat (embed1 x) = cubeToNat x + 2 ^ n := by
  unfold cubeToNat embed1
  have hlast : Fin.last n ∉ Finset.image Fin.castSucc x := by
    intro h
    rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
    have hval : (i : ℕ) = n := by simpa using congrArg Fin.val hi
    exact Nat.ne_of_lt i.isLt hval
  rw [Finset.sum_insert hlast]
  rw [Finset.sum_image]
  · simp +decide only [Fin.val_last, Fin.val_castSucc]
    exact add_comm _ _
  · intro a _ b _ h
    exact Fin.castSucc_injective n h
end BooleanIsoperimetry
