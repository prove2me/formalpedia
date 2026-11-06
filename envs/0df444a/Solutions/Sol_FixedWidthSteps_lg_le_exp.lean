-- Prove2me | solution 1 for FixedWidthSteps.lg_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:09:40.180204+00:00
-- url     : https://prove2.me/submissions/54b596b5-9883-4ba3-b998-a0a71b4d0242

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_Small
import Definitions.Def_VariableBound_Printed_ThmVariablesA
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_FixedWidthSteps_Absorb
import Theorems.Thm_FixedWidthSteps_expVariables_pos
import Theorems.Thm_FixedWidthSteps_lg_facts
import Theorems.Thm_FixedWidthSteps_timeVariables_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
import Theorems.Thm_MainTheoremForms_stepSparsifyLarge
import Theorems.Thm_VariableBound_Paper_lg_le_sub_one
import Theorems.Thm_VariableBound_VariablesA_stepSparsifyLarge
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
section
open FixedWidthSteps
open MainTheoremForms FixedWidth
namespace FixedWidthSteps
theorem _root_.solution (hSmall : SmallCasesAreWithinTheBound) (α : ℝ) (hα : 0 ≤ α) : ∃ c₁ : ℕ, 1 ≤ c₁ ∧ ∀ n : ℕ, 4 ≤ n → lg n ≤ c₁ * expVariables α n := by
  obtain ⟨n₁, h₁⟩ := MainTheoremForms.stepSparsifyLarge ⌈α⌉₊
  obtain ⟨C, hC⟩ := hSmall α 1 0 n₁ hα
  refine ⟨C + 1, by omega, fun n hn => ?_⟩
  obtain ⟨hl2, hll⟩ := lg_facts hn
  have hE := expVariables_pos α hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have e1 : ((C + 1 : ℕ) : ℝ) * expVariables α n = C * expVariables α n + expVariables α n := by push_cast; ring
  rw [e1]
  by_cases h : n₁ ≤ n
  · have h2 := h₁ 1 n (1 / lg n ^ ⌈α⌉₊) h (by norm_num; linarith) le_rfl
    have h3 : lg n ^ α ≤ lg n ^ ⌈α⌉₊ := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil α)
    have h4 : 0 < lg n ^ α := Real.rpow_pos_of_pos (by linarith) _
    have h5 : 1 / lg n ^ ⌈α⌉₊ * n ≤ expVariables α n := by
      rw [one_div_mul_eq_div]
      show (n : ℝ) / lg n ^ ⌈α⌉₊ ≤ (n : ℝ) * lg (lg n) / lg n ^ α
      exact div_le_div₀ (mul_nonneg hn0.le (by linarith)) (by nlinarith [mul_nonneg hn0.le (sub_nonneg.2 hll)]) h4 h3
    rw [Nat.cast_one, one_mul] at h2
    have := mul_nonneg hC0 hE.le
    linarith
  · have h2 := hC n hn (not_le.1 h)
    simp only [one_mul, pow_zero, mul_one] at h2
    have h3 : (2 : ℝ) ^ (n : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * expVariables α n) := by
      rw [Real.rpow_natCast]
      exact le_trans (by exact_mod_cast h2) (timeVariables_le α C n)
    have h4 : (n : ℝ) ≤ C * expVariables α n := (Real.rpow_le_rpow_left_iff one_lt_two).1 h3
    have h5 : lg n ≤ (n : ℝ) - 1 := VariableBound.Paper.lg_le_sub_one (by omega)
    linarith
end FixedWidthSteps
