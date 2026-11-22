-- Prove2me | solution 1 for DeciSigma1.Semantics.isRegularTree_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:02.372822+00:00
-- url     : https://prove2.me/submissions/16a82e1f-dd01-4526-a4d5-f715fcdf781f

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
theorem _root_.solution : IsRegularTree (PrefixSet.univ : PrefixSet n) := by
  apply (Set.finite_singleton (Set.univ : Set (List (Fin n)))).subset
  rintro _ ⟨w, rfl⟩
  simp [PrefixSet.residual, PrefixSet.univ]
end DeciSigma1.Semantics
