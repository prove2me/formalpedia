-- Prove2me | solution 1 for BooleanIsoperimetry.rank_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:13.443527+00:00
-- url     : https://prove2.me/submissions/51557f3a-37fa-45e9-99d8-20ad8ab23520

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_simplicialLe_antisymm
public import Theorems.Thm_BooleanIsoperimetry_simplicialLe_total
public import Theorems.Thm_BooleanIsoperimetry_rank_strictMono

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} : Function.Injective (@rank n) := by
  intros x y hxy
  by_contra h_neq
  -- Since $x \neq y$, by the total order property, either $x < y$ or $y < x$.
  have h_total : simplicialLt x y ∨ simplicialLt y x := by
    rcases simplicialLe_total x y with hle | hle
    · exact Or.inl ⟨hle, fun h => h_neq <| simplicialLe_antisymm _ _ hle h⟩
    · exact Or.inr ⟨hle, fun h => h_neq <| simplicialLe_antisymm _ _ h hle⟩
  obtain h | h := h_total
  · exact hxy.not_lt (rank_strictMono h)
  · exact hxy.not_gt (rank_strictMono h)
end BooleanIsoperimetry
