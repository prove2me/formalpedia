-- Prove2me | solution 1 for GJKKL.weight_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:26.977875+00:00
-- url     : https://prove2.me/submissions/42587f92-dcd3-4c15-a723-6c5fe760c95d

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
public import Theorems.Thm_GJKKL_greedyKernel_K_pos_iff
public import Theorems.Thm_GJKKL_isGreedySeq_nil
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_History_weight_nonneg
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil


attribute [local simp] GJKKL.isGreedySeq_nil
attribute [local simp] GJKKL.isGreedySeq_cons

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution {H : Finset (Finset V)} :
    ∀ {h : List (Finset V)}, 0 < weight (greedyKernel H) h ↔ IsGreedySeq H h
  | [] => by simp
  | a :: h => by
    rw [weight_cons, isGreedySeq_cons, ← solution, ← greedyKernel_K_pos_iff]
    constructor
    · intro hpos
      have h1 := weight_nonneg (greedyKernel H) h
      have h2 := (greedyKernel H).nonneg h a
      refine ⟨lt_of_le_of_ne h1 fun h0 => ?_, lt_of_le_of_ne h2 fun h0 => ?_⟩
      · rw [← h0, zero_mul] at hpos; exact lt_irrefl _ hpos
      · rw [← h0, mul_zero] at hpos; exact lt_irrefl _ hpos
    · rintro ⟨h1, h2⟩; exact mul_pos h1 h2
end GJKKL
