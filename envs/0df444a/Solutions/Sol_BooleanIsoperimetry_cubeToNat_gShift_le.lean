-- Prove2me | solution 1 for BooleanIsoperimetry.cubeToNat_gShift_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:07.08411+00:00
-- url     : https://prove2.me/submissions/e2a66b71-5b5b-4179-a9c0-fbfc94d29d46

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
theorem _root_.solution {n : ℕ} (x : Cube n) : cubeToNat (gShift x) ≤ cubeToNat x := by
  unfold gShift; by_cases hx : x.Nonempty <;>
    simp_all +decide only [Finset.not_nonempty_iff_eq_empty, Finset.not_nonempty_empty,
      ↓reduceDIte, le_refl]
  exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
end BooleanIsoperimetry
