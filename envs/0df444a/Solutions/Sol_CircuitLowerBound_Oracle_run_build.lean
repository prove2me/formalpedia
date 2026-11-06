-- Prove2me | solution 1 for CircuitLowerBound.Oracle.run_build
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:53:46.367753+00:00
-- url     : https://prove2.me/submissions/f79542a8-0981-4ba7-a2fd-868c03fc0c6c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Machine
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Runs
import Theorems.Thm_CircuitLowerBound_Oracle_run_mv
import Theorems.Thm_CircuitLowerBound_Oracle_pushed_false
import Theorems.Thm_CircuitLowerBound_Oracle_pushed_true
import Theorems.Thm_CircuitLowerBound_Oracle_run_cp
import Theorems.Thm_CircuitLowerBound_Oracle_ns_ans
import Theorems.Thm_CircuitLowerBound_Oracle_ns_io
import Theorems.Thm_CircuitLowerBound_Oracle_ns_sp
import Theorems.Thm_CircuitLowerBound_Oracle_one_self
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
theorem _root_.solution (v : M.tm.σ) (x ans : List Bool) :
    Run (stp M O) ⟨some (.inr .cpA), (v, none), stk M (one M.tm.k₀ []) (ns x ans.reverse [])⟩ (2 * ans.length + 2 * x.length + 5)
      ⟨some (.inl M.tm.main), (v, none), stk M (one M.tm.k₀ ((roundInput x ans).map M.inputAlphabet.invFun)) (ns x ans.reverse [])⟩ := by
  have r1 := run_cp O (M := M) (s := .ans) (d := .sp) (by decide) (mark := false) (me := .cpA) rfl (by decide) v ans.reverse [] (ns x ans.reverse []) rfl
  have r2 := run_mv O (M := M) (s := .sp) (d := .ans) (by decide) (me := .mvA) rfl (by decide) v (one M.tm.k₀ (ans.map M.inputAlphabet.invFun)) ans (ns x [] ans) rfl
  have r3 : Run (stp M O) ⟨some (.inr .sep), (v, none), stk M (one M.tm.k₀ (ans.map M.inputAlphabet.invFun)) (ns x ans.reverse [])⟩ 1
      ⟨some (.inr .mvX), (v, none), stk M (one M.tm.k₀ (M.inputAlphabet.invFun false :: ans.map M.inputAlphabet.invFun)) (ns x ans.reverse [])⟩ := by
    refine Run.one ?_
    rw [stp_of_ne O (by simp)]
    simp [prog, TM2.stepAux]
  have r4 := run_mv O (M := M) (s := .io) (d := .sp) (by decide) (me := .mvX) rfl (by decide) v
    (one M.tm.k₀ (M.inputAlphabet.invFun false :: ans.map M.inputAlphabet.invFun)) x (ns x ans.reverse []) rfl
  have r5 := run_cp O (M := M) (s := .sp) (d := .io) (by decide) (mark := true) (me := .cpX) rfl (by decide) v x.reverse
    (M.inputAlphabet.invFun false :: ans.map M.inputAlphabet.invFun) (ns [] ans.reverse x.reverse) rfl
  simp only [pushed_false, pushed_true, upd_io, upd_ans, upd_sp, ns_io, ns_ans, ns_sp, List.reverse_reverse, List.append_nil, List.length_reverse] at r1 r2 r4 r5
  have e : (x.flatMap fun b => [true, b]).map M.inputAlphabet.invFun ++ M.inputAlphabet.invFun false :: ans.map M.inputAlphabet.invFun
      = (roundInput x ans).map M.inputAlphabet.invFun := by simp [roundInput]
  rw [e] at r5
  have r := (((r1.trans r2).trans r3).trans r4).trans r5
  have hn : ans.length + 1 + (ans.length + 1) + 1 + (x.length + 1) + (x.length + 1) = 2 * ans.length + 2 * x.length + 5 := by ring
  rw [hn] at r
  exact r
end CircuitLowerBound.Oracle
