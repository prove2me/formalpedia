-- Prove2me | solution 1 for FromPrinted.SplitSat.core3_decides
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:51:19.440545+00:00
-- url     : https://prove2.me/submissions/bd558de5-80fb-4a78-bdf7-acb149205100

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_Printed_End
import Definitions.Def_Printed_Count
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_Enumerate_Enumeration
import Definitions.Def_Exits_Poly
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_WidthK_Top_Poly
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Core
import Theorems.Thm_FromPrinted_SplitSat_stCore3Eq
import Theorems.Thm_ClauseBound_Alg_End_length_enc_succ_le
import Theorems.Thm_CountKSat_stDecU
import Theorems.Thm_GraphProblems_runs_of_mapIn
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_satN_toN
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_SplitSat_exists_instance
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK.Prog UniformInK Paper CountKSat Eight Eight.ViaGrouping GraphProblems SplitSat
open FromPrinted FromPrinted.SplitSat
namespace FromPrinted.SplitSat
theorem _root_.solution {ℓ τ : ℕ} {δ : ℝ} (h : Paper.DecidesInSteps (Printed.SAT ℓ τ) δ) : ∃ c : ℕ, Decides3 (core3 ℓ τ) δ c := by
  obtain ⟨c, h⟩ := h
  refine ⟨c * (3 * 2 ^ 3 + 1) ^ c + (3 + 1) * c, fun N ψ hψ hnd => ?_⟩
  obtain ⟨φ, h3, rfl⟩ := exists_instance hψ hnd
  obtain ⟨T, b, hr, hb, hT⟩ := h N φ h3
  refine ⟨T, b, ?_, hb.trans (Decode.satN_toN φ).symm, hT.trans ?_⟩
  swap
  · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h1 : 1 ≤ (3 * 2 ^ 3 + 1) ^ c := Nat.one_le_pow _ _ (by omega)
    have h2 : c ≤ c * (3 * 2 ^ 3 + 1) ^ c + (3 + 1) * c := (Nat.le_mul_of_pos_right c h1).trans (Nat.le_add_right _ _)
    exact_mod_cast h2
  rw [stCore3Eq] at hr
  have hr' := runs_of_mapIn hr
  have he : decU 3 (Sat3.enc φ) = (List.replicate N (), Decode.toN φ) := stDecU 3 N φ (by omega) h3.1
  rw [he] at hr'
  refine hr'.mono le_rfl ?_
  have hl : (Sat3.enc φ).length + 1 ≤ (3 * 2 ^ 3 + 1) * (N + 2) ^ (3 + 1) := DecodeK.length_enc_succ_le (k := 3) h3
  calc c * ((Sat3.enc φ).length + 1) ^ c ≤ c * ((3 * 2 ^ 3 + 1) * (N + 2) ^ (3 + 1)) ^ c :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl c)
    _ = (c * (3 * 2 ^ 3 + 1) ^ c) * (N + 2) ^ ((3 + 1) * c) := by rw [mul_pow, ← pow_mul, mul_assoc]
    _ ≤ (c * (3 * 2 ^ 3 + 1) ^ c + (3 + 1) * c) * (N + 2) ^ (c * (3 * 2 ^ 3 + 1) ^ c + (3 + 1) * c) :=
        Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _))
end FromPrinted.SplitSat
