-- Prove2me | solution 1 for DeciSigma1.Semantics.PrefixSet.not_node_le_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:39:21.786652+00:00
-- url     : https://prove2.me/submissions/351ac802-0fca-4330-a1d8-d1e1ec1290b6

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
theorem _root_.solution (a : Fin n → PrefixSet n) : ¬ node a ≤ bot := by
  intro h
  exact mem_bot [] (h (nil_mem_node a))
end DeciSigma1.Semantics.PrefixSet
