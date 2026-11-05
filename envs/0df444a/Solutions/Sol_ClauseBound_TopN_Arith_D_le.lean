-- Prove2me | solution 1 for ClauseBound.TopN.Arith.D_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:46:29.111502+00:00
-- url     : https://prove2.me/submissions/9253a280-a9c8-4593-928e-572d535797f6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_ClauseBound_TopN_ArithR
import Theorems.Thm_ClauseBound_Alg_TopArith_le_logb_of_pow_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
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
attribute [local fun_prop] Groundwork.PolyT.all
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
theorem _root_.solution {K s C C₀ k : ℕ} {e : ℝ} (hK : 2 ≤ K) (he : 1 / Real.logb 2 K ^ C₀ ≤ e) (h2 : (2 : ℝ) ^ s ≤ (2 / e) ^ C) :
    ((2 ^ betaN k s : ℕ) : ℝ) ≤ (a0 k C : ℝ) * Real.logb 2 K ^ (4 * cK k * C * C₀) := by
  have hy1 : (1 : ℝ) ≤ Real.logb 2 K := by simpa using le_logb_of_pow_le K 1 (by simpa using hK)
  generalize Real.logb 2 K = y at he hy1 ⊢
  have hy0 : 0 < y := by linarith
  have hyC : 0 < y ^ C₀ := by positivity
  have he0 : 0 < e := lt_of_lt_of_le (by positivity) he
  have h1e : 1 ≤ e * y ^ C₀ := by rwa [div_le_iff₀ hyC] at he
  have h2e : 2 / e ≤ 2 * y ^ C₀ := by
    rw [div_le_iff₀ he0]
    nlinarith
  have hs : (2 : ℝ) ^ s ≤ (2 * y ^ C₀) ^ C := h2.trans (pow_le_pow_left₀ (by positivity) h2e C)
  have eβ : betaN k s = s * (4 * cK k) + (17 * cK k + k + 3) := by unfold betaN cK; ring
  calc ((2 ^ betaN k s : ℕ) : ℝ) = ((2 : ℝ) ^ s) ^ (4 * cK k) * 2 ^ (17 * cK k + k + 3) := by
        rw [eβ]; push_cast; rw [pow_add, pow_mul]
    _ ≤ ((2 * y ^ C₀) ^ C) ^ (4 * cK k) * 2 ^ (17 * cK k + k + 3) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hs _) (by positivity)
    _ = (a0 k C : ℝ) * y ^ (4 * cK k * C * C₀) := by
        have e1 : C * (4 * cK k) = 4 * cK k * C := by ring
        have e2 : C₀ * (4 * cK k * C) = 4 * cK k * C * C₀ := by ring
        unfold a0
        push_cast
        rw [← pow_mul, mul_pow, ← pow_mul, e1, e2]
        ring
end ClauseBound.TopN.Arith
