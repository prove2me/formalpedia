-- Prove2me | solution 1 for Falmagne.pathFlow_eq_zero_or_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:37.45384+00:00
-- url     : https://prove2.me/submissions/71c4df67-68d0-4fd5-8b45-af1f332d763d

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Path
public import Theorems.Thm_Falmagne_pathFlow_nil
public import Theorems.Thm_Falmagne_pathFlow_cons
public import Theorems.Thm_Falmagne_pathFlow_zero_of_not_mem
attribute [local simp] Falmagne.pathFlow_nil
attribute [local simp] Falmagne.pathFlow_cons

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace Falmagne
theorem _root_.solution (l : List X) (hl : l.Nodup) (x : X) (A : Finset X) :
    pathFlow l x A = 0 ∨ pathFlow l x A = 1 := by
  induction l with
  | nil => simp
  | cons y l ih =>
      obtain ⟨hyn, hln⟩ := List.nodup_cons.mp hl
      by_cases hxy : x = y
      · subst x
        rw [pathFlow_cons, pathFlow_zero_of_not_mem l hyn]
        unfold unitEdge
        split_ifs <;> simp
      · simpa [pathFlow_cons, unitEdge, hxy] using ih hln
end Falmagne
