-- Prove2me | solution 1 for DeciSigma1.Semantics.isRegularTree_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:39.356283+00:00
-- url     : https://prove2.me/submissions/921c5ebe-ba6b-4d4b-be0f-a21adf9fd0cc

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
theorem _root_.solution (a : Fin n → PrefixSet n) (ha : ∀ i, IsRegularTree (a i)) :
    IsRegularTree (PrefixSet.node a) := by
  apply ((Set.finite_singleton (PrefixSet.node a).carrier).union (Set.finite_iUnion ha)).subset
  rintro _ ⟨w, rfl⟩
  cases w with
  | nil => exact Or.inl (by simp [PrefixSet.residual])
  | cons i w => exact Or.inr (Set.mem_iUnion.mpr ⟨i, w, rfl⟩)
end DeciSigma1.Semantics
