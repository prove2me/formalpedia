-- Prove2me | solution 1 for DecisionTree.lift_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:38:53.583628+00:00
-- url     : https://prove2.me/submissions/bf1b0017-1ea4-4a95-8215-8233de2f3b34

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_DecisionTree

set_option autoImplicit true
open DecisionTree
namespace DecisionTree
theorem _root_.solution {n n' : Nat} {h : n ≤ n'} : Function.Injective (lift h) := by
  intro x y hxy
  cases x with
  | leaf _ =>
    cases y with
    | leaf _ => simp only [lift] at hxy; simp_all
    | branch _ _ _ => contradiction
  | branch _ _ _ =>
    cases y with
    | leaf _ => contradiction
    | branch _ _ _ =>
      simp only [lift] at hxy
      injection hxy with a b c
      rw [solution b, solution c]
      simp_all only [Fin.mk.injEq, DecisionTree.branch.injEq, and_self, and_true]
      ext
      simp_all only
end DecisionTree
