-- Prove2me | solution 1 for Falmagne.pathFlow_divergence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:17.669801+00:00
-- url     : https://prove2.me/submissions/207ec780-1123-4316-94d7-38f41fca4f3b

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Path
public import Theorems.Thm_Falmagne_pathFlow_nil
public import Theorems.Thm_Falmagne_pathFlow_cons
public import Theorems.Thm_Falmagne_outflow_add
public import Theorems.Thm_Falmagne_inflow_add
public import Theorems.Thm_Falmagne_outflow_unitEdge
public import Theorems.Thm_Falmagne_inflow_unitEdge
attribute [local simp] Falmagne.pathFlow_nil
attribute [local simp] Falmagne.pathFlow_cons

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace Falmagne
theorem _root_.solution (l : List X) (hl : l.Nodup) (A : Finset X) :
    outflow (pathFlow l) A - inflow (pathFlow l) A =
      (if A = l.toFinset then 1 else 0) - (if A = ∅ then 1 else 0) := by
  induction l with
  | nil => simp only [outflow, inflow, pathFlow, Finset.sum_const_zero, List.toFinset_nil]; split_ifs <;> simp_all
  | cons y l ih =>
      have hyn : y ∉ l := (List.nodup_cons.mp hl).1
      have hln : l.Nodup := (List.nodup_cons.mp hl).2
      have hy : y ∈ (y :: l).toFinset := by simp
      have herase : (y :: l).toFinset.erase y = l.toFinset := by simp [hyn]
      change outflow (fun x B => unitEdge y (y :: l).toFinset x B + pathFlow l x B) A -
        inflow (fun x B => unitEdge y (y :: l).toFinset x B + pathFlow l x B) A = _
      rw [outflow_add, inflow_add, outflow_unitEdge hy, inflow_unitEdge hy, herase]
      have hi := ih hln
      linarith
end Falmagne
