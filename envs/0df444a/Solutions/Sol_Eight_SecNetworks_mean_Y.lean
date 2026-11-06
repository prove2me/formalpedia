-- Prove2me | solution 1 for Eight.SecNetworks.mean_Y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:24:17.810306+00:00
-- url     : https://prove2.me/submissions/9939f6da-c67d-4f37-bcf1-f3baa5d2410c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Eight_SecNetworks_Grouping
import Theorems.Thm_Groundwork_Colouring_sum_Ys
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


section
namespace Eight.SecNetworks
open Finset Groundwork.Colouring
variable {g K : ℕ}
private theorem off_diag (c : Fin g → Fin g → ℕ) (a : Fin g) : off c a a = 0 := by simp [off]
private theorem off_row (c : Fin g → Fin g → ℕ) (a : Fin g) : ∑ b, off c a b = ∑ b ∈ univ.erase a, c a b := by
  unfold off
  rw [← sum_filter, filter_ne']
private theorem Us_off (c : Fin g → Fin g → ℕ) : Us (off c) = ∑ a, ∑ b ∈ univ.erase a, c a b := by
  unfold Us
  rw [Fintype.sum_prod_type]
  exact sum_congr rfl fun a _ => off_row c a
private theorem Ys_off (c : Fin g → Fin g → ℕ) {γ γ' : Fin K} (hne : γ ≠ γ') (χ : Fin g → Fin K) : Ys (off c) γ γ' χ = Y c χ γ γ' := by
  unfold Ys Y off
  rw [Fintype.sum_prod_type, sum_filter]
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : χ a = γ
  · rw [if_pos ha, sum_filter]
    refine sum_congr rfl fun b _ => ?_
    by_cases hb : χ b = γ'
    · have hba : b ≠ a := by
        rintro rfl
        exact hne (ha.symm.trans hb)
      simp [ha, hb, hba]
    · simp [hb]
  · simp [ha]
end Eight.SecNetworks
set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Finset Groundwork.Colouring
variable {g K : ℕ}
namespace Eight.SecNetworks
theorem _root_.solution (c : Fin g → Fin g → ℕ) {γ γ' : Fin K} (hne : γ ≠ γ') :
    (∑ χ : Fin g → Fin K, Y c χ γ γ') * K ^ 2 = K ^ g * ∑ a, ∑ b ∈ univ.erase a, c a b := by
  have h := sum_Ys (κ := Fin K) (off c) (off_diag c) γ γ'
  simpa only [Fintype.card_fin, Ys_off c hne, Us_off] using h
end Eight.SecNetworks
