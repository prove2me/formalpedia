-- Prove2me | solution 1 for DeciSigma1.Semantics.PrefixSet.complete_le_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:08.807809+00:00
-- url     : https://prove2.me/submissions/30038315-ad49-4f9c-8860-b152e7303dd5

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
theorem _root_.solution (d : ℕ) : complete d ≤ node fun _ => (complete d : PrefixSet n) := by
  intro w hw
  cases w with
  | nil => trivial
  | cons i w => exact lt_trans (Nat.lt_succ_self _) hw
end DeciSigma1.Semantics.PrefixSet
