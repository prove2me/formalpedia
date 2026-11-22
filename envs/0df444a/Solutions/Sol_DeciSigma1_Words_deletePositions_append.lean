-- Prove2me | solution 1 for DeciSigma1.Words.deletePositions_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:59.092542+00:00
-- url     : https://prove2.me/submissions/c2abb2be-844c-4044-8c37-0e1bfc42ccaa

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
theorem _root_.solution (xs ys : List α) :
    deletePositions (xs ++ ys) D = deletePositions xs D ++
      ((ys.zipIdx xs.length).filter (fun p => p.2 ∉ D)).map Prod.fst := by
  unfold deletePositions
  rw [List.zipIdx_append, List.filter_append, List.map_append, Nat.zero_add]
end DeciSigma1.Words
