-- Prove2me | solution 1 for Falmagne.inflow_unitEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:30.652964+00:00
-- url     : https://prove2.me/submissions/48000c02-5ee6-40cd-9c5e-88b4596473b7

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
    inflow (unitEdge y B) A = if A = B.erase y then 1 else 0 := by
  classical
  by_cases h : A = B.erase y
  · subst A
    have hy' : y ∈ Finset.univ \ B.erase y := by simp
    have hi : insert y (B.erase y) = B := Finset.insert_erase hy
    unfold inflow
    rw [Finset.sum_eq_single y]
    · simp [unitEdge, hi]
    · intro z hz hzy
      simp [unitEdge, hzy]
    · intro hy0
      exact (hy0 hy').elim
  · have hzero : ∀ z ∈ Finset.univ \ A, unitEdge y B z (insert z A) = 0 := by
      intro z hz
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hz
      unfold unitEdge
      split_ifs with heq
      · have hz' : z = y := heq.1
        subst z
        have : A = B.erase y := by rw [← heq.2]; simp [hz]
        exact (h this).elim
      · rfl
    simp [inflow, Finset.sum_eq_zero hzero, h]
end Falmagne
