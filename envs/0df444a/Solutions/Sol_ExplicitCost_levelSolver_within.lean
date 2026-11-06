-- Prove2me | solution 1 for ExplicitCost.levelSolver_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:25:32.137896+00:00
-- url     : https://prove2.me/submissions/cc11124f-6bb0-4c4e-bce5-78fca62930f4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStages
import Theorems.Thm_ExplicitCost_askInt_within
import Theorems.Thm_ExplicitCost_askList_within
import Theorems.Thm_ExplicitCost_size_le_succ
import Theorems.Thm_ExplicitCost_length_lt_size
import Theorems.Thm_ExplicitCost_capsLoop_within
import Theorems.Thm_ExplicitCost_bind_within
import Theorems.Thm_ExplicitCost_lift_within
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_length_lt_size
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_TM_update_withIO
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_QueryMachines_QueryMachine_close_bind
import Theorems.Thm_QueryMachines_QueryMachine_close_both
import Theorems.Thm_QueryMachines_QueryMachine_close_branch
import Theorems.Thm_QueryMachines_QueryMachine_close_const
import Theorems.Thm_QueryMachines_QueryMachine_close_foldRange
import Theorems.Thm_QueryMachines_QueryMachine_close_foldWhile
import Theorems.Thm_QueryMachines_QueryMachine_close_gated
import Theorems.Thm_QueryMachines_QueryMachine_close_ite
import Theorems.Thm_QueryMachines_QueryMachine_close_lift
import Theorems.Thm_QueryMachines_QueryMachine_close_mapAsk
import Theorems.Thm_QueryMachines_QueryMachine_close_mapIn
import Theorems.Thm_QueryMachines_QueryMachine_close_mapOut
import Theorems.Thm_QueryMachines_QueryMachine_close_optBind
import Theorems.Thm_QueryMachines_QueryMachine_close_prodRange
import Theorems.Thm_QueryMachines_QueryMachine_close_query
import Theorems.Thm_QueryMachines_QueryMachine_close_subst
import Theorems.Thm_QueryMachines_QueryMachine_close_sumRange
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.TM.update_withIO
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit
attribute [local simp] QueryMachines.QueryMachine.close_bind
attribute [local simp] QueryMachines.QueryMachine.close_both
attribute [local simp] QueryMachines.QueryMachine.close_branch
attribute [local simp] QueryMachines.QueryMachine.close_const
attribute [local simp] QueryMachines.QueryMachine.close_foldRange
attribute [local simp] QueryMachines.QueryMachine.close_foldWhile
attribute [local simp] QueryMachines.QueryMachine.close_gated
attribute [local simp] QueryMachines.QueryMachine.close_ite
attribute [local simp] QueryMachines.QueryMachine.close_lift
attribute [local simp] QueryMachines.QueryMachine.close_mapAsk
attribute [local simp] QueryMachines.QueryMachine.close_mapIn
attribute [local simp] QueryMachines.QueryMachine.close_mapOut
attribute [local simp] QueryMachines.QueryMachine.close_optBind
attribute [local simp] QueryMachines.QueryMachine.close_prodRange
attribute [local simp] QueryMachines.QueryMachine.close_query
attribute [local simp] QueryMachines.QueryMachine.close_subst
attribute [local simp] QueryMachines.QueryMachine.close_sumRange



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork QueryMachines Printed
variable {Q α : Type}
namespace ExplicitCost
theorem _root_.solution {c x₀ : ℕ} {O : SolQuery → Option Ans} {w : SolQuery → ℕ} {h : Head} {l S₁ : ℕ} {nums : List Unit × List Unit} (hN : (numbersM x₀).Runs h.1.tail (2 * l) S₁ nums) (I : List ℤ) (d : ℤ) (c₀ c₁ : List ℕ) (t : ℕ)
    (hI : O (Sum.inr (Sum.inr (h.2.1, .inr (.inl ())))) = some (.inr I)) (hd : O (Sum.inr (Sum.inr (h.2.1, .inl ()))) = some (.inl d)) (hl₀ : c₀.length = I.length) (hl₁ : c₁.length = I.length)
    (h₀ : ∀ j < I.length, O (Sum.inr (Sum.inr (h.2.1, .inr (.inr (.inl (false, I.getD j 0)))))) = some (.inl (c₀.getD j 0 : ℤ)))
    (h₁ : ∀ j < I.length, O (Sum.inr (Sum.inr (h.2.1, .inr (.inr (.inl (true, I.getD j 0)))))) = some (.inl (c₁.getD j 0 : ℤ)))
    (hw : ∀ q, w (Sum.inr (Sum.inr (h.2.1, q))) = t) {T₆ S₆ : ℕ} {Z : ℤ} (h₆ : (sumAndDivide c).Within O w (((((h, nums), I), d), c₀), c₁) T₆ S₆ Z) :
    (levelSolver c x₀).Within O w h (2 * l + 5 + 2 * I.length + (2 * I.length + 2) * t + T₆) (S₁ + 8 * size (((((h, nums), I), d), c₀), c₁) + S₆ + 10) Z := by
  have r₁ := lift_within (Q := SolQuery) (A := Ans) (O := O) (w := w) (Stepped.mapIn_runs (f := fun a : Head => a.1.tail) (a := h) hN)
  have r₂ := askList_within (h := fun s : Stage₁ => (Sum.inr (Sum.inr (s.1.2.1, .inr (.inl ()))) : SolQuery)) (w := w) (a := (h, nums)) hI
  have r₃ := askInt_within (h := fun s : Stage₂ => (Sum.inr (Sum.inr (s.1.1.2.1, .inl ())) : SolQuery)) (w := w) (a := ((h, nums), I)) hd
  have r₄ := capsLoop_within (tr := false) (lamU := fun s : Stage₃ => s.1.1.1.2.1) (idx := fun s : Stage₃ => s.1.2) (O := O) (w := w) (s := (((h, nums), I), d)) c₀ t hl₀ h₀ hw
  have r₅ := capsLoop_within (tr := true) (lamU := fun s : Stage₄ => s.1.1.1.1.2.1) (idx := fun s : Stage₄ => s.1.1.2) (O := O) (w := w) (s := ((((h, nums), I), d), c₀)) c₁ t hl₁ h₁ hw
  have hn : size I.length ≤ size I := by
    have h1 := length_lt_size I
    have h2 := size_le_succ I.length
    omega
  refine (bind_within r₁ (bind_within r₂ (bind_within r₃ (bind_within r₄ (bind_within r₅ h₆))))).mono ?_ ?_
  · rw [hw, hw]
    ring_nf
    omega
  · simp only [size_prod, size_inl, size_inr, asInt, asList] at hn ⊢
    omega
end ExplicitCost
