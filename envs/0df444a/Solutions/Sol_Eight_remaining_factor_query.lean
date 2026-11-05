-- Prove2me | solution 1 for Eight.remaining_factor_query
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:50:58.5311+00:00
-- url     : https://prove2.me/submissions/7a11256e-7165-49a5-a0d1-b1c834d3e8d9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecProof_NetworkDefs
import Definitions.Def_SingleBitPieces_SecProof_Cost
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_SecProof_Network
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_SatNet_pow_le_two_rpow
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
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
namespace Eight
theorem _root_.solution (C₁ c g : ℕ) {δ' : ℝ} (hδ' : 0 < δ') : ∃ A : ℕ, ∀ m : ℕ,
    (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ) ^ C₁ * (c * ((m : ℝ) + 1) ^ c) ≤ A * (2 : ℝ) ^ (δ' * m / 4) := by
  obtain ⟨D, hD⟩ := SatNet.pow_le_two_rpow (C₁ + c) (c := δ' / 4) (by positivity)
  refine ⟨⌈(C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * 7 ^ C₁ * c * D * (2 : ℝ) ^ (δ' / 4)⌉₊, fun m => ?_⟩
  have hdiv : (m + g - 1) / g ≤ m := by
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · simp
    · rw [Nat.div_le_iff_le_mul_add_pred hg]
      have : m ≤ g * m := Nat.le_mul_of_pos_left _ hg
      omega
  have hP : ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ) ≤ 7 * ((m : ℝ) + 1) := by
    have : 6 * ((m + g - 1) / g) + 1 ≤ 7 * (m + 1) := by omega
    exact_mod_cast this
  have hpow : ((m : ℝ) + 1) ^ (C₁ + c) ≤ D * ((2 : ℝ) ^ (δ' / 4) * (2 : ℝ) ^ (δ' * m / 4)) := by
    have h := hD (m + 1)
    rw [← Real.rpow_add two_pos]
    have e : δ' / 4 * ((m + 1 : ℕ) : ℝ) = δ' / 4 + δ' * m / 4 := by push_cast; ring
    rw [e] at h
    exact_mod_cast h
  calc (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ) ^ C₁ * (c * ((m : ℝ) + 1) ^ c)
      ≤ (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * (7 * ((m : ℝ) + 1)) ^ C₁ * (c * ((m : ℝ) + 1) ^ c) := by gcongr
    _ = (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * 7 ^ C₁ * c * ((m : ℝ) + 1) ^ (C₁ + c) := by rw [mul_pow, pow_add]; ring
    _ ≤ (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * 7 ^ C₁ * c * (D * ((2 : ℝ) ^ (δ' / 4) * (2 : ℝ) ^ (δ' * m / 4))) := by gcongr
    _ = (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * 7 ^ C₁ * c * D * (2 : ℝ) ^ (δ' / 4) * (2 : ℝ) ^ (δ' * m / 4) := by ring
    _ ≤ _ := by
        gcongr
        exact Nat.le_ceil _
end Eight
