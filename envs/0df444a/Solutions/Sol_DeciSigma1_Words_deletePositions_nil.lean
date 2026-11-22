-- Prove2me | solution 1 for DeciSigma1.Words.deletePositions_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:42:18.257088+00:00
-- url     : https://prove2.me/submissions/a4cf3a98-d3f6-470a-8dc9-0d0ee4ab9a32

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution : deletePositions ([] : List α) D = [] := rfl
end DeciSigma1.Words
