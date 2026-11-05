-- Prove2me | solution 1 for ClauseBound.TopN.Arith.master
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:31:12.039781+00:00
-- url     : https://prove2.me/submissions/d027f822-8974-4de2-82a2-0653489fc5e9

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
import Theorems.Thm_ClauseBound_TopN_Arith_D_le
import Theorems.Thm_ClauseBound_Alg_TopArith_le_logb_of_pow_le
import Theorems.Thm_ClauseBound_Alg_TopArith_logb_pow_le
import Theorems.Thm_ClauseBound_Alg_TopArith_size_le_two_logb
import Theorems.Thm_ClauseBound_TopN_Arith_b_le_D
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
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
    ((Wof k K s : ℕ) : ℝ) ≤ (A1 k C C₀ : ℝ) * K * e := by
  have hD := D_le (k := k) hK he h2
  have hY : (K.size : ℝ) ≤ 2 * Real.logb 2 K := size_le_two_logb K hK
  have hq := logb_pow_le K (qE k C C₀) hK
  have hy1 : (1 : ℝ) ≤ Real.logb 2 K := by simpa using le_logb_of_pow_le K 1 (by simpa using hK)
  have hA : (A1 k C C₀ : ℝ) = 2 * (a0 k C : ℝ) ^ 3 * (((qE k C C₀).factorial * 2 ^ qE k C C₀ : ℕ) : ℝ) := by
    unfold A1; push_cast; ring
  have hqe : qE k C C₀ = 3 * (4 * cK k * C * C₀) + 1 + C₀ := by unfold qE; ring
  rw [hA]
  generalize (((qE k C C₀).factorial * 2 ^ qE k C C₀ : ℕ) : ℝ) = F at hq ⊢
  rw [hqe] at hq
  generalize 4 * cK k * C * C₀ = p at hD hq
  generalize Real.logb 2 K = y at he hy1 hD hY hq
  have hy0 : 0 < y := by linarith
  have hyC : 0 < y ^ C₀ := by positivity
  have he0 : 0 < e := lt_of_lt_of_le (by positivity) he
  have h1e : 1 ≤ e * y ^ C₀ := by rwa [div_le_iff₀ hyC] at he
  have hb : ((betaN k s + 3 : ℕ) : ℝ) ≤ ((2 ^ betaN k s : ℕ) : ℝ) := by exact_mod_cast b_le_D k s
  have hW0 : ((Wof k K s : ℕ) : ℝ) = ((betaN k s + 3 : ℕ) : ℝ) ^ 2 * ((2 ^ betaN k s : ℕ) : ℝ) * (K.size : ℝ) := by
    unfold Wof; push_cast; ring
  rw [hW0]
  have hb0 : (0 : ℝ) ≤ ((betaN k s + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ ((2 ^ betaN k s : ℕ) : ℝ) := Nat.cast_nonneg _
  have hY0 : (0 : ℝ) ≤ (K.size : ℝ) := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ (a0 k C : ℝ) := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  generalize ((betaN k s + 3 : ℕ) : ℝ) = b at hb hb0 ⊢
  generalize ((2 ^ betaN k s : ℕ) : ℝ) = D at hb hD hD0 ⊢
  generalize (K.size : ℝ) = Y at hY hY0 ⊢
  generalize (a0 k C : ℝ) = a at hD ha0 ⊢
  calc b ^ 2 * D * Y ≤ D ^ 2 * D * (2 * y) := by gcongr
    _ = D ^ 3 * (2 * y) := by ring
    _ ≤ (a * y ^ p) ^ 3 * (2 * y) := by gcongr
    _ = 2 * a ^ 3 * y ^ (3 * p + 1) * 1 := by ring
    _ ≤ 2 * a ^ 3 * y ^ (3 * p + 1) * (e * y ^ C₀) := mul_le_mul_of_nonneg_left h1e (by positivity)
    _ = 2 * a ^ 3 * y ^ (3 * p + 1 + C₀) * e := by ring
    _ ≤ 2 * a ^ 3 * (F * K) * e := by gcongr
    _ = 2 * a ^ 3 * F * K * e := by ring
end ClauseBound.TopN.Arith
