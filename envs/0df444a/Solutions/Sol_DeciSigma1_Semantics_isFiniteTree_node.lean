-- Prove2me | solution 1 for DeciSigma1.Semantics.isFiniteTree_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:46.690798+00:00
-- url     : https://prove2.me/submissions/dfc740a0-0d9b-448e-ae4c-a1b3703bacdb

module
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Finite.Defs
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Nat.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_PrefixSet

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
namespace DeciSigma1.Semantics
theorem _root_.solution (a : Fin n → PrefixSet n) (ha : ∀ i, IsFiniteTree (a i)) :
    IsFiniteTree (PrefixSet.node a) := by
  apply ((Set.finite_singleton []).union
    (Set.finite_iUnion fun i => (ha i).image (List.cons i))).subset
  intro w hw
  cases w with
  | nil => exact Or.inl rfl
  | cons i w => exact Or.inr (Set.mem_iUnion.mpr ⟨i, w, hw, rfl⟩)
end DeciSigma1.Semantics
