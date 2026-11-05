-- Prove2me | solution 1 for ClauseBound.TopN.Arith.root17_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:29:07.440728+00:00
-- url     : https://prove2.me/submissions/8b6a2694-890d-4682-8240-358f8f7f1f66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_TopN_Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_ClauseBound_TopN_Arith
import Theorems.Thm_ClauseBound_Alg_TopArith_lt_length_filter_iff
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
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
attribute [local fun_prop] Groundwork.PolyT.filter
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



set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith
namespace ClauseBound.TopN.Arith
theorem _root_.solution (m : ℕ) : (root17 m).length ^ 17 ≤ m ∧ m < ((root17 m).length + 1) ^ 17 := by
  have hp : ∀ a b, a ≤ b → (fun b => decide (b ^ 17 ≤ m)) b = true → (fun b => decide (b ^ 17 ≤ m)) a = true := by
    intro a b hab hb
    simp only [decide_eq_true_eq] at hb ⊢
    exact (Nat.pow_le_pow_left hab 17).trans hb
  have key := lt_length_filter_iff (fun b => decide (b ^ 17 ≤ m)) hp (m + 1)
  have hcle : ((List.range (m + 1)).filter fun b => decide (b ^ 17 ≤ m)).length ≤ m + 1 := by
    simpa using List.length_filter_le (fun b => decide (b ^ 17 ≤ m)) (List.range (m + 1))
  have hlen : (root17 m).length = ((List.range (m + 1)).filter fun b => decide (b ^ 17 ≤ m)).length - 1 := by
    simp [root17]
  generalize ((List.range (m + 1)).filter fun b => decide (b ^ 17 ≤ m)).length = c at key hcle hlen
  simp only [decide_eq_true_eq] at key
  have hc0 : 0 < c := (key 0 (by omega)).1 (by simp)
  rw [hlen]
  constructor
  · exact (key (c - 1) (by omega)).2 (by omega)
  · have e : c - 1 + 1 = c := by omega
    rw [e]
    rcases Nat.lt_or_ge c (m + 1) with h | h
    · by_contra hcon
      have := (key c h).1 (by omega)
      omega
    · have hcm : c = m + 1 := by omega
      rw [hcm]
      calc m < m + 1 := by omega
        _ ≤ (m + 1) ^ 17 := Nat.le_self_pow (by norm_num) _
end ClauseBound.TopN.Arith
