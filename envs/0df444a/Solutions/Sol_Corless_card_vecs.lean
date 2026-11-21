-- Prove2me | solution 1 for Corless.card_vecs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:40.736627+00:00
-- url     : https://prove2.me/submissions/56c73b9a-93af-4f3e-830b-775fd83b5e20

module
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Definitions.Def_LeanPool_CorlessNilpotent_Vectors
public import Theorems.Thm_Corless_eq_of_foldVector_eq
public import Theorems.Thm_Corless_getD_step_a
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
public import Theorems.Thm_Corless_I_ne_one
public import Theorems.Thm_Corless_entrySign_I
public import Theorems.Thm_Corless_entrySign_one
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero
attribute [local simp] Corless.entrySign_I
attribute [local simp] Corless.entrySign_one



set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Corless
namespace Corless
theorem _root_.solution : ∀ k, (vecs k).card = 2 ^ k
  | 0 => by simp [vecs]
  | k + 1 => by
      classical
      rw [vecs, Finset.card_biUnion]
      · rw [Finset.sum_congr rfl (g := fun _ => 2), Finset.sum_const, solution k, smul_eq_mul,
          pow_succ, mul_comm]
        intro u _
        convert Finset.card_pair _
        intro h
        have middle := congrArg (fun w : List ℂ => w.getD u.length 1) h
        rw [getD_step_a, getD_step_a] at middle
        exact I_ne_one middle.symm
      · intro u _ v _ huv
        rw [Function.onFun, Finset.disjoint_left]
        intro w hw hw'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw hw'
        apply huv
        rcases hw with rfl | rfl <;> rcases hw' with h | h <;> exact eq_of_foldVector_eq h
end Corless
