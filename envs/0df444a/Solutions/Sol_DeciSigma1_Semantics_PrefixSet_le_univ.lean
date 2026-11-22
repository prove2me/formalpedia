-- Prove2me | solution 1 for DeciSigma1.Semantics.PrefixSet.le_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:02.671161+00:00
-- url     : https://prove2.me/submissions/413bd4e1-b67b-47cb-b957-5a9864fbe637

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
open DeciSigma1.Semantics.PrefixSet
namespace DeciSigma1.Semantics.PrefixSet
theorem _root_.solution (P : PrefixSet n) : P ≤ univ := Set.subset_univ _
end DeciSigma1.Semantics.PrefixSet
