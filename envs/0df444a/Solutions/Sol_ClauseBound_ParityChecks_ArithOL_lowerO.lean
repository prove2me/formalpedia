-- Prove2me | solution 1 for ClauseBound.ParityChecks.ArithOL.lowerO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:14.75148+00:00
-- url     : https://prove2.me/submissions/5b5b03c4-8057-4173-86aa-d815695101da

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_Budget
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_UbO_le
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_gPO_le_W
import Theorems.Thm_ClauseBound_Alg_TopArith_two_g_div
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_pow_le_n
import Theorems.Thm_ClauseBound_ParityChecks_size_blk_le
import Theorems.Thm_ClauseBound_ParityChecks_size_mul_le
import Theorems.Thm_ClauseBound_TopN_Arith_Wof_ge
import Theorems.Thm_ClauseBound_TopN_Arith_k_le_beta
import Theorems.Thm_ClauseBound_TopN_Arith_lamS_mul_le
import Theorems.Thm_ClauseBound_TopN_Arith_pow_le_n
import Theorems.Thm_ClauseBound_TopN_Arith_size_n_le
import Theorems.Thm_ClauseBound_TopN_Arith_two_g_div
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



set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith
variable {k K n s C₀ : ℕ}
namespace ClauseBound.ParityChecks.ArithOL
theorem _root_.solution (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    K * (3 * K ^ 8 * K.size) ≤ 3 * (Wof k K s * n) ∧
    K * (PbOL K n (2 ^ betaN k s) * (2 * (3 * K ^ 8) / K + 1)) ≤ 3 * GO C₀ * (Wof k K s * n) ∧
    K * ((K - 1) * lamS K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s))) ≤ (55 + 354 * k + GO C₀) * (Wof k K s * n) ∧
    3 * K ^ 8 * PbOL K n (2 ^ betaN k s) ≤ GO C₀ * (Wof k K s * n) ∧
    K * (54 * K ^ 16) ≤ 54 * (Wof k K s * n) ∧
    K * K ^ 2 ≤ Wof k K s * n ∧
    K * (C₀ * K ^ 2 * (5 * (17 * C₀ * K.size) + 16)) ≤ C₀ * (85 * C₀ + 16) * (Wof k K s * n) ∧
    K * (3 * K ^ 8 * (3 * K ^ 8) * 3 * Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1))) ≤ 27 * (4 + 17 * C₀) * (Wof k K s * n) ∧
    K * ((3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size)) ≤ (17 + 51 * C₀) * (Wof k K s * n) := by
  have hK1 : 1 ≤ K := by omega
  obtain ⟨-, -, -, w4, w5, w6, -, w8⟩ := Wof_ge (k := k) (s := s) hK1
  have hz := size_n_le hlt
  have hY : 1 ≤ K.size := Nat.size_pos.2 hK1
  have hKn : K ≤ n := by simpa using pow_le_n hK1 hn17 (j := 1) (by norm_num)
  have hn0 : 1 ≤ n := hK1.trans hKn
  have gP := gPO_le_W (k := k) (s := s) hK1 hn17 hlt
  have hUb := UbO_le (k := k) (K := K) (s := s) hn0
  have hkb : k ≤ betaN k s := k_le_beta k s
  have hsb := size_blk_le (betaN k s) n
  have hsm := size_mul_le (betaN k s) n
  obtain ⟨W, hW⟩ : ∃ W, W = Wof k K s := ⟨_, rfl⟩
  rw [← hW] at w4 w5 w6 w8 gP ⊢
  obtain ⟨b, hb⟩ : ∃ b, b = betaN k s + 3 := ⟨_, rfl⟩
  rw [← hb] at w4 w6
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = K.size := ⟨_, rfl⟩
  rw [← hYd] at w4 w5 hz hY ⊢
  obtain ⟨G, hG⟩ : ∃ G, G = GO C₀ := ⟨_, rfl⟩
  rw [← hG] at gP ⊢
  have hb1 : 1 ≤ b := by omega
  have Wn : n ≤ W * n := Nat.le_mul_of_pos_left _ w8
  have K16 : K * K ^ 16 ≤ n := by rw [← pow_succ']; exact hn17
  have a1 : b ≤ b * Y := Nat.le_mul_of_pos_right _ hY
  have a2 : 17 * C₀ * Y ≤ 17 * C₀ * (b * Y) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hb1)
  have UbW : UbOL k K n (2 ^ betaN k s) ≤ (354 * k + 54) * (W * n) := by
    have c1 : 354 * k * n * (betaN k s + 1) ≤ 354 * k * (W * n) := by
      calc 354 * k * n * (betaN k s + 1) = 354 * k * ((betaN k s + 1) * n) := by ring
        _ ≤ 354 * k * (W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ((by omega : betaN k s + 1 ≤ b).trans w6))
    have c2 : 54 * K ^ 16 ≤ 54 * (W * n) := Nat.mul_le_mul_left _ ((pow_le_n hK1 hn17 (by norm_num)).trans Wn)
    calc UbOL k K n (2 ^ betaN k s) ≤ 354 * k * n * (betaN k s + 1) + 54 * K ^ 16 := hUb
      _ ≤ 354 * k * (W * n) + 54 * (W * n) := Nat.add_le_add c1 c2
      _ = (354 * k + 54) * (W * n) := by ring
  refine ⟨?_, ?_, ?_, gP, ?_, ?_, ?_, ?_, ?_⟩
  · calc K * (3 * K ^ 8 * Y) = 3 * (Y * K ^ 9) := by ring
      _ ≤ 3 * (W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul w5 (pow_le_n hK1 hn17 (by norm_num)))
  · have h1 : K * (2 * (3 * K ^ 8) / K + 1) ≤ 3 * (3 * K ^ 8) := by
      rw [Arith.two_g_div hK1]
      have h7 : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
      have e : K * (6 * K ^ 7 + 1) = 6 * K ^ 8 + K := by ring
      omega
    calc K * (PbOL K n (2 ^ betaN k s) * (2 * (3 * K ^ 8) / K + 1)) = PbOL K n (2 ^ betaN k s) * (K * (2 * (3 * K ^ 8) / K + 1)) := by ring
      _ ≤ PbOL K n (2 ^ betaN k s) * (3 * (3 * K ^ 8)) := Nat.mul_le_mul_left _ h1
      _ = 3 * (3 * K ^ 8 * PbOL K n (2 ^ betaN k s)) := by ring
      _ ≤ 3 * (G * (W * n)) := Nat.mul_le_mul_left _ gP
      _ = 3 * G * (W * n) := by ring
  · have h1 := lamS_mul_le K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s))
    generalize lamS K (3 * K ^ 8) (UbOL k K n (2 ^ betaN k s)) (PbOL K n (2 ^ betaN k s)) = lam at h1 ⊢
    have h2 : K * (K ^ 2 * lam) ≤ K * (K ^ 2 + UbOL k K n (2 ^ betaN k s) + 3 * K ^ 8 * PbOL K n (2 ^ betaN k s)) := by
      have : 3 * K ^ 8 * PbOL K n (2 ^ betaN k s) ≤ K * (3 * K ^ 8 * PbOL K n (2 ^ betaN k s)) := Nat.le_mul_of_pos_left _ hK1
      calc K * (K ^ 2 * lam) = lam * K ^ 3 := by ring
        _ ≤ K ^ 3 + K * UbOL k K n (2 ^ betaN k s) + 3 * K ^ 8 * PbOL K n (2 ^ betaN k s) := h1
        _ ≤ K ^ 3 + K * UbOL k K n (2 ^ betaN k s) + K * (3 * K ^ 8 * PbOL K n (2 ^ betaN k s)) := Nat.add_le_add_left this _
        _ = K * (K ^ 2 + UbOL k K n (2 ^ betaN k s) + 3 * K ^ 8 * PbOL K n (2 ^ betaN k s)) := by ring
    have h3 := Nat.le_of_mul_le_mul_left h2 hK1
    have h4 : K ^ 2 ≤ W * n := (pow_le_n hK1 hn17 (by norm_num)).trans Wn
    calc K * ((K - 1) * lam) ≤ K * (K * lam) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
      _ = K ^ 2 * lam := by ring
      _ ≤ K ^ 2 + UbOL k K n (2 ^ betaN k s) + 3 * K ^ 8 * PbOL K n (2 ^ betaN k s) := h3
      _ ≤ W * n + (354 * k + 54) * (W * n) + G * (W * n) := Nat.add_le_add (Nat.add_le_add h4 UbW) gP
      _ = (55 + 354 * k + G) * (W * n) := by ring
  · calc K * (54 * K ^ 16) = 54 * (K * K ^ 16) := by ring
      _ ≤ 54 * (W * n) := Nat.mul_le_mul_left _ (K16.trans Wn)
  · calc K * K ^ 2 = K ^ 3 := by ring
      _ ≤ n := pow_le_n hK1 hn17 (by norm_num)
      _ ≤ W * n := Wn
  · have h1 : 5 * (17 * C₀ * Y) + 16 ≤ (85 * C₀ + 16) * W := by
      calc 5 * (17 * C₀ * Y) + 16 ≤ 85 * C₀ * Y + 16 * Y := by nlinarith
        _ = (85 * C₀ + 16) * Y := by ring
        _ ≤ (85 * C₀ + 16) * W := Nat.mul_le_mul_left _ w5
    calc K * (C₀ * K ^ 2 * (5 * (17 * C₀ * Y) + 16)) = C₀ * ((5 * (17 * C₀ * Y) + 16) * K ^ 3) := by ring
      _ ≤ C₀ * ((85 * C₀ + 16) * W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 (pow_le_n hK1 hn17 (by norm_num)))
      _ = C₀ * (85 * C₀ + 16) * (W * n) := by ring
  · have h2 : Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)) ≤ (4 + 17 * C₀) * W := by
      calc Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)) ≤ 2 * betaN k s + n.size + 10 := hsb
        _ ≤ 4 * (b * Y) + 17 * C₀ * (b * Y) := by omega
        _ = (4 + 17 * C₀) * (b * Y) := by ring
        _ ≤ (4 + 17 * C₀) * W := Nat.mul_le_mul_left _ w4
    calc K * (3 * K ^ 8 * (3 * K ^ 8) * 3 * Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)))
        = 27 * (Nat.size (blkOL (2 ^ betaN k s) * (7 * n + 1)) * K ^ 17) := by ring
      _ ≤ 27 * ((4 + 17 * C₀) * W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 hn17)
      _ = 27 * (4 + 17 * C₀) * (W * n) := by ring
  · have h1 : (3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size) ≤ (17 + 51 * C₀) * (b * Y) := by
      have c1 : (k + 9) * n.size ≤ 3 * b * (17 * C₀ * Y) := Nat.mul_le_mul (by omega) hz
      have e1 : (k + 3) * n.size + 6 * n.size = (k + 9) * n.size := by ring
      have c2 : 4 * betaN k s + 5 * k + 24 ≤ 17 * b := by omega
      calc (3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size)
          ≤ (4 * betaN k s + 5 * k + 24) + (k + 9) * n.size := by omega
        _ ≤ 17 * b + 3 * b * (17 * C₀ * Y) := Nat.add_le_add c2 c1
        _ ≤ 17 * (b * Y) + 3 * b * (17 * C₀ * Y) := Nat.add_le_add_right (Nat.mul_le_mul_left _ a1) _
        _ = (17 + 51 * C₀) * (b * Y) := by ring
    calc K * ((3 * Nat.size (2 ^ betaN k s * n) + 3 * n.size + 12) + 2 + (betaN k s + 5 * k + 10 + (k + 3) * n.size))
        ≤ n * ((17 + 51 * C₀) * (b * Y)) := Nat.mul_le_mul hKn h1
      _ = (17 + 51 * C₀) * (b * Y * n) := by ring
      _ ≤ (17 + 51 * C₀) * (W * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ w4)
end ClauseBound.ParityChecks.ArithOL
