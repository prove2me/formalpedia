-- Prove2me | solution 1 for FreeCode.overhead_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:47:20.431635+00:00
-- url     : https://prove2.me/submissions/36677278-8f27-4de4-8004-1aa7b820d918

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_FreeCode_Behind
import Theorems.Thm_FreeCode_length_enc_succ_le
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Paper SplitSat
namespace FreeCode
theorem _root_.solution {k n : ℕ} {φ : Sat3.CNF n} (h3 : SatK.IsKCNF k φ) (c q : ℕ) :
    ((SatFree.enc φ).length + c * (n + 2) ^ c + 1) ^ q ≤ (2 ^ k * (k + 1) + 2 + c) ^ q * (n + 2) ^ ((k + 1 + c) * q) := by
  have h1 := length_enc_succ_le h3
  obtain ⟨A, hA⟩ : ∃ A, A = 2 ^ k * (k + 1) + 2 := ⟨_, rfl⟩
  rw [← hA] at h1 ⊢
  have e1 : (n + 2) ^ (k + 1) ≤ (n + 2) ^ (k + 1 + c) := Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : (n + 2) ^ c ≤ (n + 2) ^ (k + 1 + c) := Nat.pow_le_pow_right (by omega) (by omega)
  have e3 : A * (n + 2) ^ (k + 1) ≤ A * (n + 2) ^ (k + 1 + c) := Nat.mul_le_mul_left _ e1
  have e4 : c * (n + 2) ^ c ≤ c * (n + 2) ^ (k + 1 + c) := Nat.mul_le_mul_left _ e2
  have e5 : (A + c) * (n + 2) ^ (k + 1 + c) = A * (n + 2) ^ (k + 1 + c) + c * (n + 2) ^ (k + 1 + c) := by ring
  calc ((SatFree.enc φ).length + c * (n + 2) ^ c + 1) ^ q ≤ ((A + c) * (n + 2) ^ (k + 1 + c)) ^ q := Nat.pow_le_pow_left (by omega) q
    _ = (A + c) ^ q * (n + 2) ^ ((k + 1 + c) * q) := by rw [mul_pow, ← pow_mul]
end FreeCode
