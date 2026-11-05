-- Prove2me | solution 1 for Eight.Level.levelE_le_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:18:16.744227+00:00
-- url     : https://prove2.me/submissions/e4e7fda1-4dc6-45e6-b0f1-3eda8a8910be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_SecPseudocode_Levels
import Mathlib.Tactic
import Definitions.Def_Eight_SecPseudocode_Levels
import Theorems.Thm_Eight_Level_rho_pos
import Theorems.Thm_Eight_Level_rho_lt_one
import Theorems.Thm_Eight_Level_rho_ge
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
import Theorems.Thm_SingleBitPieces_SecPseudocode_Levels_levelK_pos
import Theorems.Thm_SingleBitPieces_SecPseudocode_Levels_levelK_succ_ge
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
open Eight Eight.Level
open Paper SingleBitPieces.SecPseudocode_Levels
namespace Eight.Level
theorem _root_.solution (ℓ : ℕ) : levelE ℓ ≤ 0.56 * rho ^ ℓ - 3.8 / levelK ℓ := by
  induction ℓ with
  | zero => norm_num [levelE, levelK]
  | succ ℓ ih =>
    have hK := levelK_pos ℓ
    have hK' := levelK_pos (ℓ + 1)
    have hρ0 := rho_pos
    have hρ7 := rho_ge
    have hρ1 : rho ^ ℓ ≤ 1 := pow_le_one₀ hρ0.le rho_lt_one.le
    have hρp : 0 < rho ^ ℓ := pow_pos hρ0 ℓ
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / levelK ℓ := ⟨_, rfl⟩
    have ha0 : 0 < a := by rw [ha]; positivity
    have hb : 3.8 / (levelK (ℓ + 1) : ℝ) ≤ 0.2 * a := by
      rw [ha, div_le_iff₀ hK']
      have h := levelK_succ_ge ℓ
      have e : 0.2 * (1 / (levelK ℓ : ℝ)) * (levelK (ℓ + 1) : ℝ) = 0.2 * ((levelK (ℓ + 1) : ℝ) / levelK ℓ) := by ring
      rw [e]
      have h2 : 19 ≤ (levelK (ℓ + 1) : ℝ) / levelK ℓ := (le_div_iff₀ hK).2 h
      linarith
    have e1 : (2 : ℝ) / levelK ℓ = 2 * a := by rw [ha]; ring
    have e2 : (3.8 : ℝ) / levelK ℓ = 3.8 * a := by rw [ha]; ring
    rw [e2] at ih
    simp only [levelE]
    rw [e1, pow_succ]
    have h1 : (rho + 2 * a) * levelE ℓ ≤ (rho + 2 * a) * (0.56 * rho ^ ℓ - 3.8 * a) := mul_le_mul_of_nonneg_left ih (by positivity)
    have h2 : 0 ≤ a * a := by positivity
    have h3 : a * rho ^ ℓ ≤ a := by nlinarith
    have h4 : 7 / 8 * a ≤ rho * a := by nlinarith
    nlinarith
end Eight.Level
