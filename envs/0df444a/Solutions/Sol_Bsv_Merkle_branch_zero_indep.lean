-- Prove2me | solution 1 for Bsv.Merkle.branch_zero_indep
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T11:41:28.997809+00:00
-- url     : https://prove2.me/submissions/87c13871-697c-4fde-a48f-5a723867800e

import Definitions.Def_bsv_merkle_tree
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

open Bsv.Merkle


theorem solution {α : Type} (H : α → α → α) (x y : α) (t : List α) :
    branch H (x :: t) 0 = branch H (y :: t) 0 := by
  induction hn : t.length using Nat.strongRecOn generalizing t x y with
  | _ n ih =>
    match t, hn with
    | [], _ => simp [branch]
    | b :: t', hn =>
      rw [branch, branch]
      simp only [sib, Nat.zero_div, level]
      congr 1
      exact ih _ (by subst hn; simp only [length_level, List.length_cons]; omega) _ _ _ rfl
