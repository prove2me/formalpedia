-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.NoSuffixOccurrenceEndsBetween.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:42.829792+00:00
-- url     : https://prove2.me/submissions/1fb00486-b163-40af-9551-14b77a3eba1c

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
public import Theorems.Thm_DeciSigma1_Words_occurrences_antitone


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
namespace NoSuffixOccurrenceEndsBetween
theorem _root_.solution [DecidableEq α] {x t : List α} {b B c c' : ℕ}
    (h : NoSuffixOccurrenceEndsBetween x t b c c')
    (hb : b ≤ B) : NoSuffixOccurrenceEndsBetween x t B c c' :=
  fun e he => h e (Words.occurrences_antitone hb he)
end NoSuffixOccurrenceEndsBetween
end DeciSigma1.Holes.Tail
