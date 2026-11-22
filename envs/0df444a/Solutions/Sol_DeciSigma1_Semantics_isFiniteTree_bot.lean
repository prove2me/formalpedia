-- Prove2me | solution 1 for DeciSigma1.Semantics.isFiniteTree_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:41.305813+00:00
-- url     : https://prove2.me/submissions/50359079-474e-4ec4-a921-ceba9065d7e6

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
theorem _root_.solution : IsFiniteTree (PrefixSet.bot : PrefixSet n) := Set.finite_empty
end DeciSigma1.Semantics
