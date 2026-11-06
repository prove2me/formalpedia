-- Prove2me | solution 1 for Eight.SecNetworks.var_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:07.724804+00:00
-- url     : https://prove2.me/submissions/b530a3f6-c607-4695-bae2-bf6c52b6a0c5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Eight_SecNetworks_Grouping
import Theorems.Thm_Eight_SecNetworks_mean_size
import Theorems.Thm_Groundwork_Colouring_Zs_eq
import Theorems.Thm_Groundwork_Colouring_sum_Zs_sq
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


section
namespace Eight.SecNetworks
open Finset Groundwork.Colouring
variable {g K : ℕ}
private theorem var_of_moments {Ω : Type} [Fintype Ω] (X : Ω → ℕ) (A m V : ℕ) (S1 : (∑ χ, X χ) * A = Fintype.card Ω * m)
    (S2 : (∑ χ, X χ ^ 2) * A ^ 2 ≤ Fintype.card Ω * m ^ 2 + V) : ∑ χ, ((A : ℤ) * X χ - m) ^ 2 ≤ V := by
  zify at S1 S2
  have hsum : ∑ χ : Ω, ((A : ℤ) * X χ - m) ^ 2 = (∑ χ : Ω, (X χ : ℤ) ^ 2) * A ^ 2 - 2 * m * ((∑ χ : Ω, (X χ : ℤ)) * A) + (Fintype.card Ω : ℤ) * m ^ 2 := by
    have : ∀ χ : Ω, ((A : ℤ) * X χ - m) ^ 2 = (X χ : ℤ) ^ 2 * A ^ 2 - 2 * m * ((X χ : ℤ) * A) + (m : ℤ) ^ 2 := by
      intro χ; ring
    simp only [this, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
  rw [hsum, S1]
  linarith
end Eight.SecNetworks
set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Finset Groundwork.Colouring
variable {g K : ℕ}
namespace Eight.SecNetworks
theorem _root_.solution (γ : Fin K) : ∑ χ : Fin g → Fin K, ((K : ℤ) * (#{a | χ a = γ} : ℕ) - (g : ℤ)) ^ 2 ≤ ((g * K * K ^ g : ℕ) : ℤ) := by
  have S2 := sum_Zs_sq (ι := Fin g) γ
  simp only [Fintype.card_fin, Zs_eq] at S2
  refine var_of_moments (fun χ : Fin g → Fin K => #{a | χ a = γ}) K g _ ?_ ?_
  · rw [mean_size]; simp [mul_comm]
  · simpa [mul_comm] using S2
end Eight.SecNetworks
