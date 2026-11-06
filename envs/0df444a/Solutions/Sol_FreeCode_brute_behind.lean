-- Prove2me | solution 1 for FreeCode.brute_behind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:55:15.762092+00:00
-- url     : https://prove2.me/submissions/fbb79e7d-fb15-49f4-b5e7-a2587efd3837

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
import Theorems.Thm_FreeCode_bruteCore_runs
import Theorems.Thm_Groundwork_Decode_mem_toN
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_SplitSat_length_le_of_nodup
import Theorems.Thm_SplitSat_nodup_toN
import Theorems.Thm_SplitSat_size_node_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Paper SplitSat
namespace FreeCode
theorem _root_.solution {dec : List Bool → List Unit × Fml} (hdec : Reads dec) (k : ℕ) (n : ℕ) (φ : Sat3.CNF n) (h3 : SatK.IsKCNF k φ) :
    ∃ b : Bool, (Stepped.mapIn dec bruteCore).Runs (SatFree.enc φ) (2 * 2 ^ n)
      ((2 * (2 ^ k * (2 * k + 1) + 3) + k + 16) * (n + 2) ^ (2 * (2 ^ k * (2 * k + 1) + 3) + k + 16)) b ∧ (b = true ↔ Sat3.Satisfiable φ) := by
  obtain ⟨b, r, hb⟩ := bruteCore_runs φ
  refine ⟨b, Stepped.mapIn_runs ?_, hb⟩
  rw [hdec n φ]
  refine r.mono le_rfl ?_
  have hψ : ∀ D ∈ Decode.toN φ, D.length ≤ k ∧ ∀ l ∈ D, l.1 < n := fun D hD => by
    obtain ⟨⟨C, hC, hl⟩, h'⟩ := Decode.mem_toN hD
    exact ⟨hl ▸ h3.1 C hC, h'⟩
  have hs := SplitSat.size_node_le (SplitSat.length_le_of_nodup hψ (SplitSat.nodup_toN h3.2)) hψ
  obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ k * (2 * k + 1) + 3 := ⟨_, rfl⟩
  rw [← hP] at hs ⊢
  have e1 : n + 2 ≤ (n + 2) ^ (k + 1) := Nat.le_self_pow (by omega) _
  have e2 : (n + 2) ^ (k + 1) ≤ (n + 2) ^ (2 * P + k + 16) := Nat.pow_le_pow_right (by omega) (by omega)
  have e3 : (2 * P + k + 16) * (n + 2) ^ (k + 1) ≤ (2 * P + k + 16) * (n + 2) ^ (2 * P + k + 16) := Nat.mul_le_mul_left _ e2
  have e4 : (2 * P + k + 16) * (n + 2) ^ (k + 1) = 2 * (P * (n + 2) ^ (k + 1)) + k * (n + 2) ^ (k + 1) + 16 * (n + 2) ^ (k + 1) := by ring
  omega
end FreeCode
