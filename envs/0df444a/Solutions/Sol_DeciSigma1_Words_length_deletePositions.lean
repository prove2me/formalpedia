-- Prove2me | solution 1 for DeciSigma1.Words.length_deletePositions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:47:07.101418+00:00
-- url     : https://prove2.me/submissions/113076e2-b7cf-4768-a0b7-4b70389264d3

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions_take

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (w : List α) :
    (deletePositions w D).length = retainedCount D w.length := by
  have := length_deletePositions_take (D := D) w (le_refl w.length)
  rwa [List.take_length] at this
end DeciSigma1.Words
