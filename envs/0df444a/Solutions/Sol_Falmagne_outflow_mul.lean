-- Prove2me | solution 1 for Falmagne.outflow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:24:51.718917+00:00
-- url     : https://prove2.me/submissions/6ca11c52-8b05-4f8a-b109-b72a32c1ce06

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
theorem _root_.solution (a : ℝ) (q : X → Finset X → ℝ) (A : Finset X) :
    outflow (fun x B => a * q x B) A = a * outflow q A := by
  simp [outflow, Finset.mul_sum]
end Falmagne
