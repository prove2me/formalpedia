-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffix_dictSuffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:56:31.165642+00:00
-- url     : https://prove2.me/submissions/da385136-8a7f-4310-96b5-a202761ab30c

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_dictSuffix_suffix
public import Theorems.Thm_DeciSigma1_Holes_Tail_length_le_length_dictSuffix

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
theorem _root_.solution {w s : List α} (hs : s <:+ w) (hsD : s ∈ D) : s <:+ dictSuffix D w :=
  List.suffix_of_suffix_length_le hs (dictSuffix_suffix D w) (length_le_length_dictSuffix hs hsD)
end DeciSigma1.Holes.Tail
