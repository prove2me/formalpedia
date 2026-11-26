-- Prove2me | solution 1 for Bsv.Merkle.mutatedCS_eq_mutatedTree
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T14:28:49.070486+00:00
-- url     : https://prove2.me/submissions/8bcb0dd6-76f3-44a5-aa4c-06e8f3f344c2

import Definitions.Def_bsv_merkle_mutation
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

namespace Bsv.Merkle.Proof_mutatedCS_eq_mutatedTree

section

variable {α : Type} (H : α → α → α)

end

section

variable {α : Type} [DecidableEq α] (H : α → α → α)

theorem mutCounter_none : ∀ (l : List α) (s : List (Option α)),
    mutCounter H l (none :: s) = (eqPair l || mutCounter H (pairs H l) s)
  | [], _ => by simp [mutCounter, eqPair, pairs]
  | [_], _ => by simp [mutCounter, eqPair, pairs, insertMut]
  | a :: b :: t, s => by
    simp only [mutCounter, insertMut, insert, eqPair, pairs, Bool.false_or,
      mutCounter_none t (insert H (H a b) s)]
    cases (a == b) <;> cases insertMut H (H a b) s <;> cases eqPair t <;> simp

theorem mutCounter_nil (a b : α) (t : List α) :
    mutCounter H (a :: b :: t) [] =
      (eqPair (a :: b :: t) || mutCounter H (pairs H (a :: b :: t)) []) := by
  simp only [mutCounter, insertMut, insert, eqPair, pairs, Bool.false_or, mutCounter_none]
  cases (a == b) <;> cases eqPair t <;> simp

theorem mutatedCS_eq_mutatedTree (l : List α) : mutatedCS H l = mutatedTree H l := by
  unfold mutatedCS
  induction hn : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    match l, hn with
    | [], _ => simp [mutCounter, mutatedTree]
    | [a], _ => simp [mutCounter, mutatedTree, insertMut]
    | a :: b :: t, hn =>
      rw [mutCounter_nil, mutatedTree]
      congr 1
      exact ih _ (by subst hn; simp only [length_pairs, List.length_cons]; omega) _ rfl

end

end Bsv.Merkle.Proof_mutatedCS_eq_mutatedTree

open Bsv.Merkle

theorem solution {α : Type} [DecidableEq α] (H : α → α → α) (l : List α) :
    mutatedCS H l = mutatedTree H l :=
  Bsv.Merkle.Proof_mutatedCS_eq_mutatedTree.mutatedCS_eq_mutatedTree H l
