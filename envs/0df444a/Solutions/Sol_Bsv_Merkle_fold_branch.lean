-- Prove2me | solution 1 for Bsv.Merkle.fold_branch
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T11:42:01.463424+00:00
-- url     : https://prove2.me/submissions/cb3b3981-524e-45fd-9094-7adfe705ac3a

import Definitions.Def_bsv_merkle_tree
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

open Bsv.Merkle

namespace Bsv.Merkle.Proof_fold_branch

variable {α : Type} (H : α → α → α)

theorem xor_one (j : Nat) : j ^^^ 1 = if j % 2 = 0 then j + 1 else j - 1 := by
  have hd : (j ^^^ 1) / 2 = j / 2 := by rw [Nat.xor_div_two]; simp
  have hm : (j ^^^ 1) % 2 = 1 ↔ ¬ (j % 2 = 1 ↔ 1 % 2 = 1) := Nat.xor_mod_two_eq_one
  by_cases h : j % 2 = 0
  · have : (j ^^^ 1) % 2 = 1 := hm.mpr (by omega)
    simp only [h, ite_true]; omega
  · have : ¬ (j ^^^ 1) % 2 = 1 := fun hx => (hm.mp hx) (by omega)
    simp only [h, ite_false]; omega

/-- The parent of the node at position `i` is the verifier's step from it. -/
theorem level_get : ∀ (l : List α) (i : Nat) (x : α), l[i]? = some x →
    (level H l)[i / 2]? = some (step H x (sib l i) i)
  | [], _, _, h => by simp at h
  | [a], i, x, h => by
    match i, h with
    | 0, h =>
      have : a = x := by simpa using h
      subst this
      simp [level, sib, step]
    | j + 1, h => simp at h
  | a :: b :: t, 0, x, h => by
    have : a = x := by simpa using h
    subst this
    simp [level, sib, step]
  | a :: b :: t, 1, x, h => by
    have : b = x := by simpa using h
    subst this
    simp [level, sib, step]
  | a :: b :: t, j + 2, x, h => by
    have hj : t[j]? = some x := by simpa using h
    have ih := level_get t j x hj
    have hx : (j + 2) ^^^ 1 = (j ^^^ 1) + 2 := by
      rw [xor_one, xor_one]
      by_cases hm : j % 2 = 0
      · have : (j + 2) % 2 = 0 := by omega
        simp [hm, this]
      · have : ¬ (j + 2) % 2 = 0 := by omega
        simp only [hm, this, ite_false]; omega
    have hd : (j + 2) / 2 = j / 2 + 1 := by omega
    have hp : (j + 2) % 2 = j % 2 := by omega
    have hs : sib (a :: b :: t) (j + 2) = sib t j := by simp [sib, hx]
    rw [hs, hd]
    simp only [level, List.getElem?_cons_succ, ih]
    cases sib t j <;> simp [step, hp]

end Bsv.Merkle.Proof_fold_branch

open Bsv.Merkle.Proof_fold_branch

theorem solution {α : Type} (H : α → α → α) (l : List α) (i : Nat) (x : α) (hx : l[i]? = some x) :
    some (fold H x (branch H l i) i) = root H l := by
  induction hn : l.length using Nat.strongRecOn generalizing l i x with
  | _ n ih =>
    match l, hn, hx with
    | [], _, hx => simp at hx
    | [a], _, hx =>
      match i, hx with
      | 0, hx =>
        have : a = x := by simpa using hx
        subst this
        simp [branch, fold, root]
      | j + 1, hx => simp at hx
    | a :: b :: t, hn, hx =>
      have hg := level_get H (a :: b :: t) i x hx
      rw [branch, root, fold]
      exact ih _ (by subst hn; simp only [length_level, List.length_cons]; omega) _ _ _ hg rfl
