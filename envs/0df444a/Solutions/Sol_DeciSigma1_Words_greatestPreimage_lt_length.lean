-- Prove2me | solution 1 for DeciSigma1.Words.greatestPreimage_lt_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:47:47.382263+00:00
-- url     : https://prove2.me/submissions/b0a7f418-8146-4e94-b54d-1955f204ee60

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions
public import Theorems.Thm_DeciSigma1_Words_le_greatestPreimage_iff

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (w : List α) {a : ℕ} (ha : a < (deletePositions w D).length) :
    greatestPreimage D a < w.length := by
  by_contra h
  have := le_greatestPreimage_iff.mp (Nat.le_of_not_lt h)
  rw [length_deletePositions] at ha
  omega
end DeciSigma1.Words
