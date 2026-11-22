-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.dictSuffix_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:45:40.651822+00:00
-- url     : https://prove2.me/submissions/45ec63e6-4ac4-483b-a571-92bfc362070d

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] {D : Finset (List α)}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (D : Finset (List α)) : ∀ w : List α, dictSuffix D w <:+ w
  | [] => List.suffix_refl _
  | a :: w => by
    rw [dictSuffix]
    split_ifs
    · exact List.suffix_refl _
    · exact (solution D w).trans (List.suffix_cons _ _)
end DeciSigma1.Holes.Tail
