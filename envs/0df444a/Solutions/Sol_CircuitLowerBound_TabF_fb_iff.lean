-- Prove2me | solution 1 for CircuitLowerBound.TabF.fb_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:49:54.552203+00:00
-- url     : https://prove2.me/submissions/bb1f0613-0385-465f-8b53-bd649261bf16

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_CircuitLowerBound_TabF_G_eq
import Theorems.Thm_CircuitLowerBound_TabF_sat_iff_testBit
import Theorems.Thm_CircuitLowerBound_TabF_tryAll_iff
import Theorems.Thm_CircuitLowerBound_TabF_length_tab_codeOf_le
import Theorems.Thm_CircuitLowerBound_TabF_two_pow_nb_le
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
attribute [local fun_prop] Groundwork.PolyT.length
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
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]
namespace CircuitLowerBound.TabF
theorem _root_.solution (hV : StVars) (m : ℕ) (hm : pos m = top (nu m)) :
    fb (List.replicate m ()) = true ↔ Fits (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m) ∧ Sat (tabF (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m)) := by
  obtain ⟨a, ha⟩ : ∃ a, a = nu m := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = 2 ^ a := ⟨_, rfl⟩
  have htop : top a = 2 ^ 2 ^ L := by rw [top, hL]
  -- m is at least 2·2^a times `pos m`
  have h1 : 2 ^ a * 2 * pos m ≤ m := by
    rw [pos, ← ha, Nat.div_div_eq_div_mul]
    exact Nat.mul_div_le _ _
  have h2 : 2 ^ L < 2 ^ 2 ^ L := Nat.pow_lt_pow_right (by norm_num) Nat.lt_two_pow_self
  have h3 : 1 ≤ L := hL ▸ Nat.one_le_two_pow
  have h4 : 2 ^ 2 ^ L ≤ m := by
    rw [← ha, htop] at hm
    rw [hm, ← hL] at h1
    nlinarith
  have h5 : L ≤ m := by
    have : L < 2 ^ L := Nat.lt_two_pow_self
    omega
  have h6 : a ≤ m := by
    have : a < 2 ^ a := Nat.lt_two_pow_self
    omega
  simp only [fb, List.length_replicate, ← ha, ← hL, min_eq_left h5, Bool.and_eq_true, decide_eq_true_eq]
  refine and_congr_right fun hF => ?_
  have hpad : 2 ^ nb (codeOf a) L ≤ (List.replicate ((2 * m + 1) * m) ()).length := by
    rw [List.length_replicate]
    refine (two_pow_nb_le hF).trans (Nat.mul_le_mul ?_ (by omega))
    have := length_tab_codeOf_le a
    omega
  rw [G_eq hF hpad, tryAll_iff, sat_iff_testBit _ (2 ^ L) (hV _ _ _ hF), hm, ← ha, htop]
end CircuitLowerBound.TabF
