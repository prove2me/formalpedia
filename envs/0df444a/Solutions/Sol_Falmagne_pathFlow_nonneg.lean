-- Prove2me | solution 1 for Falmagne.pathFlow_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:35.769998+00:00
-- url     : https://prove2.me/submissions/7e2d1fe6-8d5d-4de8-8e24-8e42a5d20602

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
theorem _root_.solution (l : List X) (x : X) (A : Finset X) :
    0 ≤ pathFlow l x A := by
  induction l with
  | nil => simp
  | cons y l ih =>
      rw [pathFlow_cons]
      have h : 0 ≤ unitEdge y (y :: l).toFinset x A := by unfold unitEdge; split <;> norm_num
      exact add_nonneg h ih
end Falmagne
