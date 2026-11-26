-- Prove2me | solution 1 for Falmagne.outflow_unitEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:07.817712+00:00
-- url     : https://prove2.me/submissions/bb4cbfc0-7429-4a97-b04a-13a4c4880c9c

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
theorem _root_.solution (hy : y ∈ B) (A : Finset X) :
    outflow (unitEdge y B) A = if A = B then 1 else 0 := by
  classical
  by_cases h : A = B
  · subst A
    simp [outflow, unitEdge, hy]
  · simp [outflow, unitEdge, h]
end Falmagne
