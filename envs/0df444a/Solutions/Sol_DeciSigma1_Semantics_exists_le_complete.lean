-- Prove2me | solution 1 for DeciSigma1.Semantics.exists_le_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:50.441807+00:00
-- url     : https://prove2.me/submissions/1af6039c-6c60-44e0-8fa4-b70aa466e55b

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
theorem _root_.solution {ι : Type*} [Finite ι] {t : ι → PrefixSet n}
    (ht : ∀ i, IsFiniteTree (t i)) : ∃ d, ∀ i, t i ≤ PrefixSet.complete d := by
  obtain ⟨d, hd⟩ := ((Set.finite_iUnion ht).image List.length).bddAbove
  exact ⟨d + 1, fun i w hw =>
    Nat.lt_succ_of_le (hd ⟨w, Set.mem_iUnion.mpr ⟨i, hw⟩, rfl⟩)⟩
end DeciSigma1.Semantics
