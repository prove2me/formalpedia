-- Prove2me | solution 1 for DeciSigma1.Semantics.isRegularTree_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:34.211231+00:00
-- url     : https://prove2.me/submissions/4c6c2e5a-59ad-4eed-8316-d929d05588e5

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
theorem _root_.solution : IsRegularTree (PrefixSet.bot : PrefixSet n) := by
  apply (Set.finite_singleton (∅ : Set (List (Fin n)))).subset
  rintro _ ⟨w, rfl⟩
  simp [PrefixSet.residual, PrefixSet.bot]
end DeciSigma1.Semantics
