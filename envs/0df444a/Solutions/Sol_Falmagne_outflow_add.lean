-- Prove2me | solution 1 for Falmagne.outflow_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:24:44.415506+00:00
-- url     : https://prove2.me/submissions/e5bbe209-89c3-4f82-be8d-6197a6d56afb

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
theorem _root_.solution (q r : X → Finset X → ℝ) (A : Finset X) :
    outflow (fun x B => q x B + r x B) A = outflow q A + outflow r A := by
  simp [outflow, Finset.sum_add_distrib]
end Falmagne
