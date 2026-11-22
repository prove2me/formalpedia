-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.mem_suffixDictionary_of_infix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:40:45.933808+00:00
-- url     : https://prove2.me/submissions/d4f50464-3a9f-477d-b21d-2bc8f2b226df

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_mem_suffixDictionary
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
variable [DecidableEq α]
variable {ts : List (List α)} {B : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {u v : List α} (hv : v ∈ suffixDictionary ts B)
    (hu : u <:+: v) : u ∈ suffixDictionary ts B := by
  rcases mem_suffixDictionary.mp hv with rfl | ⟨t, ht, h⟩
  · exact mem_suffixDictionary.mpr (.inl (List.infix_nil.mp hu))
  · exact mem_suffixDictionary.mpr (.inr ⟨t, ht, hu.trans h⟩)
end DeciSigma1.Holes.Tail
