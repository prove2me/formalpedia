-- Prove2me | solution 1 for FreeCode.stBrute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:36:51.118358+00:00
-- url     : https://prove2.me/submissions/7f22343b-5c62-4414-a8fa-c6df062f04f2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Definitions.Def_FreeCode_ReaderCert
import Definitions.Def_FreeCode_Behind
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SplitSat_Sizes
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Basic
import Batteries.Data.Nat.Lemmas
import Mathlib.Tactic
import Definitions.Def_FreeCode_Brute
import Theorems.Thm_FreeCode_bruteCore_polyTimeSteps
import Theorems.Thm_FreeCode_brute_behind
import Theorems.Thm_FreeCode_overhead_le
import Theorems.Thm_FreeCode_readFree_polyT
import Theorems.Thm_FreeCode_reads_readFree
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SplitSat_exists_simulates
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Paper SplitSat
namespace FreeCode
theorem _root_.solution : StBrute := by
  have hp : PolyTimeSteps (Stepped.mapIn readFree bruteCore) := by
    obtain ⟨h⟩ := bruteCore_polyTimeSteps
    exact ⟨IsPolyT.mapIn readFree_polyT⟩
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates _ hp
  refine ⟨readFree, M, q, readFree_polyT, reads_readFree, hfin, hp, fun k => ?_, hs, fun k => ?_⟩
  · refine ⟨2 * (2 ^ k * (2 * k + 1) + 3) + k + 16, fun n φ h3 => ?_⟩
    obtain ⟨b, r, hb⟩ := brute_behind reads_readFree k n φ h3
    exact ⟨2 * 2 ^ n, b, r, hb, Nat.mul_le_mul_right _ (by omega)⟩
  · obtain ⟨c, hc⟩ : ∃ c, c = 2 * (2 ^ k * (2 * k + 1) + 3) + k + 16 := ⟨_, rfl⟩
    obtain ⟨G, hG⟩ : ∃ G, G = (2 ^ k * (k + 1) + 2 + c) ^ q := ⟨_, rfl⟩
    refine ⟨3 * q * G + (k + 1 + c) * q, fun n φ h3 => ?_⟩
    obtain ⟨b, r, hb⟩ := brute_behind reads_readFree k n φ h3
    rw [← hc] at r
    obtain ⟨ev⟩ := hs _ b _ _ r
    refine ⟨b, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩⟩
    have hpow := overhead_le h3 c q
    rw [← hG] at hpow
    have e0 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have e1 : 2 * 2 ^ n + 1 ≤ 3 * 2 ^ n := by omega
    have e2 : (n + 2) ^ ((k + 1 + c) * q) ≤ (n + 2) ^ (3 * q * G + (k + 1 + c) * q) := Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _)
    calc q * (2 * 2 ^ n + 1) * ((SatFree.enc φ).length + c * (n + 2) ^ c + 1) ^ q
        ≤ q * (3 * 2 ^ n) * (G * (n + 2) ^ (3 * q * G + (k + 1 + c) * q)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ e1) (hpow.trans (Nat.mul_le_mul_left _ e2))
      _ = 3 * q * G * (n + 2) ^ (3 * q * G + (k + 1 + c) * q) * 2 ^ n := by ring
      _ ≤ (3 * q * G + (k + 1 + c) * q) * (n + 2) ^ (3 * q * G + (k + 1 + c) * q) * 2 ^ n :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
end FreeCode
