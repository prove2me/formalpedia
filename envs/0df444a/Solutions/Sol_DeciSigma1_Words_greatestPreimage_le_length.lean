-- Prove2me | solution 1 for DeciSigma1.Words.greatestPreimage_le_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:48:08.952521+00:00
-- url     : https://prove2.me/submissions/4f3a074f-d6e7-4a0e-b5c0-c7ee0979cc63

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_mono
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_length
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (w : List α) (hD : w.length ∉ D) {a : ℕ}
    (ha : a ≤ (deletePositions w D).length) : greatestPreimage D a ≤ w.length :=
  (greatestPreimage_mono ha).trans (greatestPreimage_length w hD).le
end DeciSigma1.Words
