-- Prove2me | solution 1 for Bsv.Merkle.rootCS_eq_root
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T14:28:08.052803+00:00
-- url     : https://prove2.me/submissions/67a5edfa-5d60-4d0f-952c-916a7fa33f35

import Definitions.Def_bsv_merkle_counter
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

namespace Bsv.Merkle.Proof_rootCS_eq_root

section

variable {α : Type} (H : α → α → α)

theorem level_eq : ∀ l : List α,
    level H l = pairs H l ++ (match odd l with | none => [] | some z => [H z z])
  | [] => by simp [level, pairs, odd]
  | [_] => by simp [level, pairs, odd]
  | _ :: _ :: t => by simp [level, pairs, odd, level_eq t]

theorem length_odd : ∀ l : List α, (odd l).isSome = (l.length % 2 == 1)
  | [] => by simp [odd]
  | [_] => by simp [odd]
  | _ :: _ :: t => by simp only [odd, List.length_cons, length_odd t]; congr 1; omega

theorem counter_cons (a : α) (t : List α) (s : List (Option α)) :
    counter H (a :: t) s = counter H t (insert H a s) := rfl

theorem counter_append (p : List α) (h : α) (s : List (Option α)) :
    counter H (p ++ [h]) s = insert H h (counter H p s) := by
  simp [counter, List.foldl_append]

theorem counter_none : ∀ (l : List α) (s : List (Option α)),
    counter H l (none :: s) = odd l :: counter H (pairs H l) s
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, s => by
    simp only [counter_cons, insert, pairs, odd]
    exact counter_none t _

theorem counter_nil (a b : α) (t : List α) :
    counter H (a :: b :: t) [] = odd (a :: b :: t) :: counter H (pairs H (a :: b :: t)) [] := by
  simp only [counter_cons, insert, pairs, odd]
  exact counter_none H t _

theorem insert_any (h : α) : ∀ s : List (Option α), (insert H h s).any Option.isSome = true
  | [] => by simp [insert]
  | none :: _ => by simp [insert]
  | some x :: s => by simp [insert, insert_any (H x h) s]

theorem counter_any : ∀ (l : List α) (s : List (Option α)),
    s.any Option.isSome = true → (counter H l s).any Option.isSome = true
  | [], _, h => h
  | a :: t, s, _ => by
    rw [counter_cons]; exact counter_any t _ (insert_any H a s)

theorem not_all_none_of_any_some : ∀ c : List (Option α),
    c.any Option.isSome = true → c.all Option.isNone = false
  | [], h => by simp at h
  | some _ :: _, _ => by simp
  | none :: c, h => by
    have := not_all_none_of_any_some c (by simpa using h)
    simpa using this

theorem counter_not_all_none (a : α) (t : List α) :
    (counter H (a :: t) []).all Option.isNone = false :=
  not_all_none_of_any_some _ (counter_any H t _ (insert_any H a []))

theorem carry_eq : ∀ (s : List (Option α)) (h : α),
    some (carry H h s) = finish H (insert H h s)
  | [], h => by simp [carry, insert, finish, top]
  | some x :: s, h => by simp only [carry, insert, finish]; exact carry_eq s _
  | none :: s, h => by simp [carry, insert, finish, top]

theorem rootCS_eq_root (l : List α) : rootCS H l = root H l := by
  unfold rootCS
  induction hn : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    match l, hn with
    | [], _ => simp [counter, finish, root]
    | [a], _ => simp [counter, insert, finish, top, root]
    | a :: b :: t, hn =>
      have hlen := length_pairs H (a :: b :: t)
      rw [counter_nil, root, level_eq]
      cases ho : odd (a :: b :: t) with
      | none =>
        simp only [finish, List.append_nil]
        exact ih _ (by subst hn; rw [hlen]; simp only [List.length_cons]; omega) _ rfl
      | some z =>
        have hne : (counter H (pairs H (a :: b :: t)) []).all Option.isNone = false := by
          simp only [pairs]; exact counter_not_all_none H _ _
        simp only [finish, top, hne, Bool.false_eq_true, ite_false]
        rw [carry_eq, ← counter_append]
        have hodd := length_odd (a :: b :: t)
        rw [ho] at hodd
        simp only [Option.isSome_some, List.length_cons] at hodd
        have hodd' : (t.length + 1 + 1) % 2 = 1 := by simpa using hodd.symm
        exact ih _ (by
          subst hn
          simp only [List.length_append, hlen, List.length_cons, List.length_nil]
          omega) _ rfl

end

end Bsv.Merkle.Proof_rootCS_eq_root

open Bsv.Merkle

theorem solution {α : Type} (H : α → α → α) (l : List α) :
    rootCS H l = root H l :=
  Bsv.Merkle.Proof_rootCS_eq_root.rootCS_eq_root H l
