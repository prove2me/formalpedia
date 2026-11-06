-- Prove2me | solution 1 for CircuitLowerBound.Oracle.run_round
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:59:22.941973+00:00
-- url     : https://prove2.me/submissions/1428919c-4f3d-45ec-a61f-631ec1cf2a88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Machine
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Runs
import Theorems.Thm_CircuitLowerBound_Oracle_run_build
import Theorems.Thm_CircuitLowerBound_Oracle_liftCfg_init
import Theorems.Thm_CircuitLowerBound_Oracle_liftCfg_halt
import Theorems.Thm_CircuitLowerBound_Oracle_ns_ans
import Theorems.Thm_CircuitLowerBound_Oracle_ns_io
import Theorems.Thm_CircuitLowerBound_Oracle_ns_sp
import Theorems.Thm_CircuitLowerBound_Oracle_one_self
import Theorems.Thm_CircuitLowerBound_Oracle_run_lift
import Theorems.Thm_CircuitLowerBound_Oracle_run_of_iterate
import Theorems.Thm_CircuitLowerBound_Oracle_stk_inl
import Theorems.Thm_CircuitLowerBound_Oracle_stk_inr
import Theorems.Thm_CircuitLowerBound_Oracle_stp_of_ne
import Theorems.Thm_CircuitLowerBound_Oracle_upd_ans
import Theorems.Thm_CircuitLowerBound_Oracle_upd_io
import Theorems.Thm_CircuitLowerBound_Oracle_upd_sp
import Theorems.Thm_CircuitLowerBound_Oracle_update_inl
import Theorems.Thm_CircuitLowerBound_Oracle_update_inr
import Theorems.Thm_CircuitLowerBound_Oracle_update_one
import Theorems.Thm_Groundwork_TM_Run_one
import Theorems.Thm_Groundwork_TM_Run_trans
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
attribute [local simp] CircuitLowerBound.Oracle.ns_ans
attribute [local simp] CircuitLowerBound.Oracle.ns_io
attribute [local simp] CircuitLowerBound.Oracle.ns_sp
attribute [local simp] CircuitLowerBound.Oracle.one_self
attribute [local simp] CircuitLowerBound.Oracle.stk_inl
attribute [local simp] CircuitLowerBound.Oracle.stk_inr
attribute [local simp] CircuitLowerBound.Oracle.upd_ans
attribute [local simp] CircuitLowerBound.Oracle.upd_io
attribute [local simp] CircuitLowerBound.Oracle.upd_sp
attribute [local simp] CircuitLowerBound.Oracle.update_inl
attribute [local simp] CircuitLowerBound.Oracle.update_inr
attribute [local simp] CircuitLowerBound.Oracle.update_one
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



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable {M : TM2ComputableAux Bool Bool} (O : Lang)
namespace CircuitLowerBound.Oracle
theorem _root_.solution {T : ℕ} {x ans : List Bool} {c : Bool} {w : List Bool} (h : Round M T x ans (c :: w)) :
    ∃ t ≤ 2 * ans.length + 2 * x.length + T + 6,
      Run (stp M O) ⟨some (.inr .cpA), (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns x ans.reverse [])⟩ t
        ⟨some (if c then .inr .ask else .inr .drX), (M.tm.initialState, none),
          stk M (one M.tm.k₁ (w.map M.outputAlphabet.invFun)) (ns x ans.reverse [])⟩ := by
  obtain ⟨E⟩ := h
  have r1 := run_build O (M := M) M.tm.initialState x ans
  have r2 := run_lift O (ns x ans.reverse []) (run_of_iterate E.evals_in_steps)
  rw [liftCfg_init, liftCfg_halt] at r2
  have r3 : Run (stp M O) ⟨some (.inr .after), (M.tm.initialState, none), stk M (one M.tm.k₁ ((c :: w).map M.outputAlphabet.invFun)) (ns x ans.reverse [])⟩ 1
      ⟨some (if c then .inr .ask else .inr .drX), (M.tm.initialState, none),
        stk M (one M.tm.k₁ (w.map M.outputAlphabet.invFun)) (ns x ans.reverse [])⟩ := by
    refine Run.one ?_
    rw [stp_of_ne O (by simp)]
    cases c <;> simp [prog, TM2.stepAux]
  refine ⟨_, ?_, (r1.trans r2).trans r3⟩
  have := E.steps_le_m
  omega
end CircuitLowerBound.Oracle
