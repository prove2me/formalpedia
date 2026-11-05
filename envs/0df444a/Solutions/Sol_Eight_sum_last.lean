-- Prove2me | solution 1 for Eight.sum_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:24.219225+00:00
-- url     : https://prove2.me/submissions/f4f86514-a7c7-479b-865b-e9296da01e2c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Chunk
import Theorems.Thm_Eight_blkAt_append_right
import Theorems.Thm_Eight_sum_words_three
import Theorems.Thm_Eight_sum_words_six
import Theorems.Thm_Eight_off_eq_lenW
import Theorems.Thm_Groundwork_PolyT_length
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
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
namespace Eight
theorem _root_.solution (tr : Bool) (t : ℕ) (Q a b a' b' : List Bool) {u : List Bool} (hu : u.length = lenW tr Q t) :
    ∑ v ∈ words (if wide tr Q t = true then 6 else 3), topAt tr Q (u ++ v) a b t * botAt tr Q (u ++ v) a' b' t =
      if wide tr Q t = true then Rb (blkL a t) (blkL a' t) (blkL b t) (blkL b' t) else Rb (blkL a t) (blkL b t) (blkL a' t) (blkL b' t) := by
  have h0 : ∀ v, blkAt (u ++ v) (lenW tr Q t) = blkAt v 0 := fun v => by rw [← hu]; exact blkAt_append_right u v 0
  have h3 : ∀ v, blkAt (u ++ v) (lenW tr Q t + 3) = blkAt v 3 := fun v => by rw [← hu]; exact blkAt_append_right u v 3
  unfold topAt botAt
  simp only [off_eq_lenW, h0, h3]
  split_ifs with hw
  · rw [sum_words_six fun k k' => (if blkL a t = k ∧ blkL b t = k' then (1 : ℤ) else 0) * Rb k (blkL a' t) k' (blkL b' t)]
    simp [ite_and]
  · rw [sum_words_three fun k => psi k (blkL a t) (blkL b t) * psi k (blkL b' t) (blkL a' t)]
    rfl
end Eight
