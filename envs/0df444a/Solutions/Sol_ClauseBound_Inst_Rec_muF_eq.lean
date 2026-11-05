-- Prove2me | solution 1 for ClauseBound.Inst.Rec.muF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:18:31.953692+00:00
-- url     : https://prove2.me/submissions/6cf3c91d-53fa-4b5f-be8c-85ac5970f07a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Data
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_CountRow
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_RecArith
import Theorems.Thm_ClauseBound_Inst_Rec_nbF_eq
import Theorems.Thm_ClauseBound_Inst_Rec_nbF_le
import Theorems.Thm_ClauseBound_Inst_Rec_sumN_eq
import Theorems.Thm_ClauseBound_Rec_card_blk_le
import Theorems.Thm_ClauseBound_Rec_mu_eq
import Theorems.Thm_Groundwork_PolyT_congr
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
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Rec
open Finset Polynomial Groundwork PaddedDescent.F ClauseBound.Rec
namespace ClauseBound.Inst.Rec
theorem _root_.solution (lam h : ℕ) : muF lam h = Pieces.mu lam h := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · have h0 : Pieces.nblk lam 0 = 0 := Nat.div_zero _
    simp [muF, Pieces.mu, Pieces.odd, h0]
  · rw [mu_eq lam hh, muF, sumN_eq]
    have key : (∑ b ∈ range (Pieces.nblk lam h), (2 ^ nbF lam h b - 1) * 2 ^ (lam - nbF lam h b)) * 2 ^ h =
        (∑ b ∈ range (Pieces.nblk lam h), (2 ^ #(Pieces.blk lam h b) - 1) * 2 ^ (h - #(Pieces.blk lam h b))) * 2 ^ lam := by
      rw [sum_mul, sum_mul]
      refine sum_congr rfl fun b _ => ?_
      have h1 := nbF_le lam h b
      have h2 := card_blk_le (n := lam) hh b
      rw [nbF_eq] at h1 ⊢
      rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
      congr 2
      omega
    rw [← Nat.mul_div_mul_right _ _ (Nat.pow_pos (n := h) (by norm_num : 0 < 2)), key, pow_succ, pow_succ,
      show 2 ^ lam * 2 * 2 ^ h = 2 ^ h * 2 * 2 ^ lam by ring, Nat.mul_div_mul_right _ _ (Nat.pow_pos (by norm_num))]
end ClauseBound.Inst.Rec
