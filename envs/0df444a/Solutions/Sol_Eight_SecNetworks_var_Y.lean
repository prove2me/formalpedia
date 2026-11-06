-- Prove2me | solution 1 for Eight.SecNetworks.var_Y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:29:54.413246+00:00
-- url     : https://prove2.me/submissions/8da58eed-54b3-420b-b6f8-de4df0a3c582

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Eight_SecNetworks_Grouping
import Theorems.Thm_Eight_SecNetworks_mean_Y
import Theorems.Thm_Groundwork_Colouring_sum_Ys_sq
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
private theorem off_symm {c : Fin g → Fin g → ℕ} (hs : ∀ a b, c a b = c b a) (a b : Fin g) : off c a b = off c b a := by
  simp only [off, hs a b, ne_comm]
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
theorem _root_.solution {c : Fin g → Fin g → ℕ} (hs : ∀ a b, c a b = c b a) {P : ℕ} (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) {γ γ' : Fin K} (hne : γ ≠ γ') :
    ∑ χ : Fin g → Fin K, (((K ^ 2 : ℕ) : ℤ) * (Y c χ γ γ' : ℕ) - ((∑ a, ∑ b ∈ univ.erase a, c a b : ℕ) : ℤ)) ^ 2
      ≤ ((4 * P * (∑ a, ∑ b ∈ univ.erase a, c a b) * K ^ 4 * K ^ g : ℕ) : ℤ) := by
  have S1 := mean_Y c hne
  have S2 := sum_Ys_sq (κ := Fin K) (off c) (off_diag c) (off_symm hs) P (fun a => by rw [off_row]; exact hP a) γ γ'
  simp only [Fintype.card_fin, Ys_off c hne, Us_off] at S2
  generalize (∑ a, ∑ b ∈ univ.erase a, c a b) = U at S1 S2 ⊢
  refine var_of_moments (fun χ : Fin g → Fin K => Y c χ γ γ') (K ^ 2) U _ (by simpa using S1) ?_
  rw [← pow_mul]
  have h2 : K ^ 2 ≤ K ^ 4 := by
    rcases Nat.eq_zero_or_pos K with h | h
    · simp [h]
    · exact Nat.pow_le_pow_right h (by omega)
  calc (∑ χ : Fin g → Fin K, Y c χ γ γ' ^ 2) * K ^ (2 * 2) ≤ K ^ g * U ^ 2 + 4 * K ^ 2 * K ^ g * P * U := S2
    _ = K ^ g * U ^ 2 + 4 * P * U * K ^ 2 * K ^ g := by ring
    _ ≤ K ^ g * U ^ 2 + 4 * P * U * K ^ 4 * K ^ g := by gcongr
    _ = Fintype.card (Fin g → Fin K) * U ^ 2 + 4 * P * U * K ^ 4 * K ^ g := by simp
end Eight.SecNetworks
