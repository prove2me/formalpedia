-- Prove2me | solution 1 for ClauseBound.Alg.Need.fitsG_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:44:41.760918+00:00
-- url     : https://prove2.me/submissions/88703efd-2d2e-4ca4-bc46-e4c2e2125d27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_Need
import Theorems.Thm_ClauseBound_Alg_Need_le_of_size_le
import Theorems.Thm_ClauseBound_Alg_Need_pow_le_of_le
import Theorems.Thm_ClauseBound_Alg_Need_pow_le_two_pow_size
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
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Need
open PaddedDescent.F
namespace ClauseBound.Alg.Need
theorem _root_.solution (P : PiecesF) {F n : ℕ} (hF : 2 ^ n ≤ F) : ∀ (sched : List Step) (Kup lam B cnt z : ℕ),
    needG P Kup lam B cnt z sched ≤ n → FitsG P F Kup lam B cnt z sched
  | [], Kup, lam, B, cnt, z, h => by
    simp only [needG, max_le_iff] at h
    exact ⟨le_of_size_le hF h.1.1, pow_le_of_le hF h.2⟩
  | s :: r, Kup, lam, B, cnt, z, h => by
    simp only [needG, max_le_iff] at h
    obtain ⟨⟨h0, -⟩, ⟨⟨h1, h2⟩, h3, h4⟩, ⟨h5, h6⟩, h7⟩ := h
    refine ⟨le_of_size_le hF h0, ?_, solution P hF r _ _ _ _ _ h7⟩
    exact
      { pieces := pow_le_of_le hF h1
        pat := le_of_size_le hF h2
        col := (pow_le_two_pow_size _ _).trans (pow_le_of_le hF h3)
        st := pow_le_of_le hF ((Nat.mul_le_mul_left _ (Nat.le_succ _)).trans h4)
        lab := pow_le_of_le hF ((Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans h4)
        tab := pow_le_of_le hF h5
        enumLab := fun ht => by
          rw [if_pos ht] at h6
          exact pow_le_of_le hF ((le_max_left _ _).trans h6)
        enumSt := fun ht => by
          rw [if_pos ht] at h6
          exact pow_le_of_le hF ((le_max_right _ _).trans h6) }
end ClauseBound.Alg.Need
