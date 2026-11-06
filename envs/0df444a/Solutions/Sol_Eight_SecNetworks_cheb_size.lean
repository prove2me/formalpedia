-- Prove2me | solution 1 for Eight.SecNetworks.cheb_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:37:24.687986+00:00
-- url     : https://prove2.me/submissions/b354a43b-8c26-4e91-a54f-2c585705bcce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Eight_SecNetworks_Grouping
import Theorems.Thm_Eight_SecNetworks_var_size
import Theorems.Thm_Groundwork_Colouring_cheb
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
private theorem cheb_count {Ω : Type} [Fintype Ω] (X : Ω → ℕ) (A m V t s : ℕ) (hV : ∑ χ, ((A : ℤ) * X χ - m) ^ 2 ≤ V) :
    #{χ : Ω | t * m + s < t * (A * X χ)} * s ^ 2 ≤ t ^ 2 * V := by
  have hc := cheb (fun χ : Ω => (t : ℤ) * ((A : ℤ) * X χ - m)) s (by positivity)
  have hsub : #{χ : Ω | t * m + s < t * (A * X χ)} ≤ #{χ : Ω | (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * X χ - m)} := by
    refine card_le_card fun χ h => ?_
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    zify at h
    linarith
  have hsum : ∑ χ : Ω, ((t : ℤ) * ((A : ℤ) * X χ - m)) ^ 2 = (t : ℤ) ^ 2 * ∑ χ : Ω, ((A : ℤ) * X χ - m) ^ 2 := by
    simp only [mul_pow, mul_sum]
  rw [hsum] at hc
  have a1 : (#{χ : Ω | t * m + s < t * (A * X χ)} : ℤ) * (s : ℤ) ^ 2 ≤ (#{χ : Ω | (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * X χ - m)} : ℤ) * (s : ℤ) ^ 2 :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hsub) (sq_nonneg _)
  have a2 : (t : ℤ) ^ 2 * ∑ χ : Ω, ((A : ℤ) * X χ - m) ^ 2 ≤ (t : ℤ) ^ 2 * V := mul_le_mul_of_nonneg_left hV (sq_nonneg _)
  have a3 := a1.trans (hc.trans a2)
  exact_mod_cast a3
end Eight.SecNetworks
set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Finset Groundwork.Colouring
variable {g K : ℕ}
namespace Eight.SecNetworks
theorem _root_.solution (γ : Fin K) : g * #{χ : Fin g → Fin K | 2 * g < K * #{a | χ a = γ}} ≤ K * K ^ g := by
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · subst h0; simp
  have hc := cheb_count (fun χ : Fin g → Fin K => #{a | χ a = γ}) K g _ 1 g (var_size γ)
  have e : ∀ χ : Fin g → Fin K, (1 * g + g < 1 * (K * #{a | χ a = γ})) ↔ (2 * g < K * #{a | χ a = γ}) := fun χ => by omega
  simp only [e] at hc
  have : (g * #{χ : Fin g → Fin K | 2 * g < K * #{a | χ a = γ}}) * g ≤ (K * K ^ g) * g := by
    calc _ = #{χ : Fin g → Fin K | 2 * g < K * #{a | χ a = γ}} * g ^ 2 := by ring
      _ ≤ 1 ^ 2 * (g * K * K ^ g) := hc
      _ = (K * K ^ g) * g := by ring
  exact Nat.le_of_mul_le_mul_right this hpos
end Eight.SecNetworks
