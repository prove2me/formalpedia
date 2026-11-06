-- Prove2me | solution 1 for CircuitLowerBound.Oracle.haltList_otm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:55:18.890241+00:00
-- url     : https://prove2.me/submissions/e038cd7f-2c35-4f0e-9bf9-4a582f3a24aa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Runs
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Restart
import Theorems.Thm_CircuitLowerBound_Oracle_one_nil_apply
import Theorems.Thm_CircuitLowerBound_Oracle_haltList_self
import Theorems.Thm_CircuitLowerBound_Oracle_haltList_ne
import Theorems.Thm_CircuitLowerBound_Oracle_ns_ans
import Theorems.Thm_CircuitLowerBound_Oracle_ns_io
import Theorems.Thm_CircuitLowerBound_Oracle_ns_sp
import Theorems.Thm_CircuitLowerBound_Oracle_one_self
import Theorems.Thm_CircuitLowerBound_Oracle_stk_inl
import Theorems.Thm_CircuitLowerBound_Oracle_stk_inr
import Theorems.Thm_CircuitLowerBound_Oracle_upd_ans
import Theorems.Thm_CircuitLowerBound_Oracle_upd_io
import Theorems.Thm_CircuitLowerBound_Oracle_upd_sp
import Theorems.Thm_CircuitLowerBound_Oracle_update_inl
import Theorems.Thm_CircuitLowerBound_Oracle_update_inr
import Theorems.Thm_CircuitLowerBound_Oracle_update_one
import Theorems.Thm_Groundwork_TM_Run_one
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
open CircuitLowerBound
open ENP Turing Groundwork.TM
open CircuitLowerBound.Oracle
variable {M : TM2ComputableAux Bool Bool}
namespace CircuitLowerBound.Oracle
theorem _root_.solution (b : Bool) :
    haltList (otm M).tm [(otm M).out.symm b] = (⟨none, (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns [b] [] [])⟩ : Cf M) := by
  have hs : (haltList (otm M).tm [(otm M).out.symm b]).stk = stk M (one M.tm.k₀ []) (ns [b] [] []) := by
    funext k
    rcases k with k | j
    · rw [stk_inl, one_nil_apply]
      exact haltList_ne (otm M).tm _ (show (Sum.inl k : M.tm.K ⊕ NS) ≠ Sum.inr NS.io by simp)
    · cases j
      · exact haltList_self (otm M).tm _
      · exact haltList_ne (otm M).tm _ (show (Sum.inr NS.ans : M.tm.K ⊕ NS) ≠ Sum.inr NS.io by simp)
      · exact haltList_ne (otm M).tm _ (show (Sum.inr NS.sp : M.tm.K ⊕ NS) ≠ Sum.inr NS.io by simp)
  exact congrArg (fun S => (⟨none, (M.tm.initialState, none), S⟩ : Cf M)) hs
end CircuitLowerBound.Oracle
