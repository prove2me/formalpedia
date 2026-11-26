-- Prove2me | solution 1 for Falmagne.inflow_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:24:51.076953+00:00
-- url     : https://prove2.me/submissions/ecbe3177-d878-4cb8-a9b8-a8b364233c4c

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
    inflow (fun x B => q x B - r x B) A = inflow q A - inflow r A := by
  simp [inflow, Finset.sum_sub_distrib]
end Falmagne
