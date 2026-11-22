-- Prove2me | solution 1 for DeciSigma1.Semantics.isFiniteTree_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:47.502375+00:00
-- url     : https://prove2.me/submissions/f37eeaf7-edf3-4c86-ba12-d28e61877499

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
theorem _root_.solution (d : ℕ) : IsFiniteTree (PrefixSet.complete d : PrefixSet n) :=
  List.finite_length_lt (Fin n) d
end DeciSigma1.Semantics
