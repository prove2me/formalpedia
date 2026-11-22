-- Prove2me | solution 1 for DeciSigma1.Words.greatestPreimage_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:47:42.61443+00:00
-- url     : https://prove2.me/submissions/04a24b77-d38a-4a60-a038-093788bec7de

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_retainedCount

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (w : List α) (hD : w.length ∉ D) :
    greatestPreimage D (deletePositions w D).length = w.length := by
  rw [length_deletePositions, greatestPreimage_retainedCount hD]
end DeciSigma1.Words
