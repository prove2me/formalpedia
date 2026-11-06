-- Prove2me | solution 1 for FreeCode.length_enc_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:36:59.624512+00:00
-- url     : https://prove2.me/submissions/50eeb101-635d-4f03-a5cb-bae75d1c9062

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FreeCode_Code
import Theorems.Thm_FreeCode_length_clauses_le
import Theorems.Thm_Groundwork_DecodeK_IsKCNF_length_le
import Theorems.Thm_Groundwork_Decode_bitLen_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
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
import Theorems.Thm_Sat3_Is3CNF_length_le
attribute [local fun_prop] Groundwork.PolyT.length
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
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)
namespace FreeCode
theorem _root_.solution {k n : ℕ} {φ : CNF n} (h : SatK.IsKCNF k φ) : (SatFree.enc φ).length + 1 ≤ (2 ^ k * (k + 1) + 2) * (n + 2) ^ (k + 1) := by
  have h1 := length_clauses_le φ h.1
  have h2 : φ.length ≤ 2 ^ k * (n + 2) ^ k := by
    calc φ.length ≤ (2 * n + 1) ^ k := DecodeK.IsKCNF.length_le h
      _ ≤ (2 * (n + 2)) ^ k := Nat.pow_le_pow_left (by omega) k
      _ = 2 ^ k * (n + 2) ^ k := mul_pow _ _ _
  have h3 : 2 + k * (Nat.log2 (2 * n) + 2) ≤ (k + 1) * (n + 2) := by
    have a1 : k * (Nat.log2 (2 * n) + 2) ≤ k * (n + 2) := Nat.mul_le_mul_left _ (by have := bitLen_le n; omega)
    have a2 : (k + 1) * (n + 2) = k * (n + 2) + (n + 2) := by ring
    omega
  have h4 : φ.length * (2 + k * (Nat.log2 (2 * n) + 2)) ≤ 2 ^ k * (k + 1) * (n + 2) ^ (k + 1) := by
    calc φ.length * (2 + k * (Nat.log2 (2 * n) + 2)) ≤ 2 ^ k * (n + 2) ^ k * ((k + 1) * (n + 2)) := Nat.mul_le_mul h2 h3
      _ = 2 ^ k * (k + 1) * (n + 2) ^ (k + 1) := by ring
  have h5 : n + 2 ≤ (n + 2) ^ (k + 1) := Nat.le_self_pow (by omega) _
  have h6 : (2 ^ k * (k + 1) + 2) * (n + 2) ^ (k + 1) = 2 ^ k * (k + 1) * (n + 2) ^ (k + 1) + 2 * (n + 2) ^ (k + 1) := by ring
  simp only [SatFree.enc, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega
end FreeCode
