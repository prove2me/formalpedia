-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.dictSuffix_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:21.861854+00:00
-- url     : https://prove2.me/submissions/f7e56109-25bc-4b06-848e-832d7e2fb26f

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_dictSuffix_mem
public import Theorems.Thm_DeciSigma1_Holes_Tail_length_le_length_dictSuffix
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffix_dictSuffix
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm


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
theorem _root_.solution (hD : [] ∈ D) {w s : List α} (hs : s <:+ w) (hsD : s ∈ D)
    (hmax : ∀ r, r <:+ w → r ∈ D → r.length ≤ s.length) : dictSuffix D w = s := by
  have h1 := hmax _ (dictSuffix_suffix D w) (dictSuffix_mem hD w)
  have h2 := length_le_length_dictSuffix (D := D) hs hsD
  exact ((suffix_dictSuffix hs hsD).eq_of_length (by omega)).symm
end DeciSigma1.Holes.Tail
