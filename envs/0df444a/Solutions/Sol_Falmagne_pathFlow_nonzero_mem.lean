-- Prove2me | solution 1 for Falmagne.pathFlow_nonzero_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:40.155052+00:00
-- url     : https://prove2.me/submissions/478394ad-0b6b-4e30-86a9-6e8d49a3a677

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Path
public import Theorems.Thm_Falmagne_pathFlow_nil
public import Theorems.Thm_Falmagne_pathFlow_cons
attribute [local simp] Falmagne.pathFlow_nil
attribute [local simp] Falmagne.pathFlow_cons

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace Falmagne
theorem _root_.solution (l : List X) (hp : pathFlow l x A ≠ 0) : x ∈ A := by
  induction l with
  | nil => simp at hp
  | cons y l ih =>
      by_cases hu : unitEdge y (y :: l).toFinset x A = 0
      · rw [pathFlow_cons, hu, zero_add] at hp
        exact ih hp
      · have heq : x = y ∧ A = (y :: l).toFinset := by simpa [unitEdge] using hu
        rcases heq with ⟨rfl, rfl⟩
        simp
end Falmagne
