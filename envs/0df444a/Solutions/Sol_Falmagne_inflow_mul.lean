-- Prove2me | solution 1 for Falmagne.inflow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:23:50.632607+00:00
-- url     : https://prove2.me/submissions/bdabe952-1472-4f08-98af-621c66530cc4

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Path

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace Falmagne
theorem _root_.solution (a : ℝ) (q : X → Finset X → ℝ) (A : Finset X) :
    inflow (fun x B => a * q x B) A = a * inflow q A := by
  unfold inflow
  rw [Finset.mul_sum]
end Falmagne
