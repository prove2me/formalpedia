-- Prove2me | solution 1 for Coding.stCubic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:42:15.036241+00:00
-- url     : https://prove2.me/submissions/71f638cd-acee-4722-bc25-3aa33d2acb7e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Sets
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
open Coding
open Finset
namespace Coding
theorem _root_.solution : StCubic := by
  intro n Φ
  have hU : (univ : Finset (Sat3.Lit n)).card = 2 * n := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm]
  have hsub : Φ.clauses ⊆ powersetCard 1 univ ∪ powersetCard 2 univ ∪ powersetCard 3 univ := by
    intro E hE
    have h1 := Finset.card_pos.2 (Φ.nonempty E hE)
    have h2 := Φ.width E hE
    simp only [mem_union, mem_powersetCard, subset_univ, true_and]
    omega
  have h := (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
  rw [card_powersetCard, card_powersetCard, card_powersetCard, hU] at h
  have c1 := Nat.choose_le_pow (2 * n) 1
  have c2 := Nat.choose_le_pow (2 * n) 2
  have c3 := Nat.choose_le_pow (2 * n) 3
  have e1 : (2 * n) ^ 1 = 2 * n := by ring
  have e2 : (2 * n) ^ 2 = 4 * n ^ 2 := by ring
  have e3 : (2 * n) ^ 3 = 8 * n ^ 3 := by ring
  have p2 : n ^ 2 ≤ n ^ 3 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Nat.pow_le_pow_right hn (by omega)
  have p1 : n ≤ n ^ 3 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · calc n = n ^ 1 := (pow_one n).symm
        _ ≤ n ^ 3 := Nat.pow_le_pow_right hn (by omega)
  omega
end Coding
