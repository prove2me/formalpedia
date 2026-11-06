-- Prove2me | solution 1 for FixedWidthSteps.everyChoiceCountsFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:36:58.589006+00:00
-- url     : https://prove2.me/submissions/3d7c75bc-09f3-4546-9ab6-1ca9ed58d397

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_Absorb
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_FixedWidthSteps_Choice
import Theorems.Thm_FixedWidthSteps_timeVariablesAAlpha_le
import Theorems.Thm_ClauseBound_Alg_End_length_enc_succ_le
import Theorems.Thm_FixedWidthSteps_absorb
import Theorems.Thm_FixedWidthSteps_expVariables_pos
import Theorems.Thm_FixedWidthSteps_lg_le_exp
import Theorems.Thm_FixedWidthSteps_timeVariables_le
import Theorems.Thm_FixedWidthSteps_two_rpow_mono
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
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
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_UniformInK_Time_length_enc_succ_le
import Theorems.Thm_VariableBound_Paper_absorb
import Theorems.Thm_Wrap_Outputs_mono
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
open FixedWidthSteps
open Turing Groundwork ClauseBound.Alg MainTheoremForms TwoMachines PairsToBound FixedWidth Wrap
namespace FixedWidthSteps
theorem _root_.solution : EveryChoiceCountsFrom := by
  intro hVariablesA hCond hSmall hW Idx _ S e C₀ Q α a hα he M C' hM Mb c hMb pre test hpre htest N q hN k hk
  obtain ⟨C1, h1⟩ := hVariablesA Idx S e C₀ Q α a hα he M C' hM
  obtain ⟨n₀, hn₀⟩ := hCond (max k 3) (S.K (Q.idx 0))
  obtain ⟨C2, h2⟩ := hSmall α c k n₀ hα.le
  obtain ⟨c₁, hc₁, hB⟩ := lg_le_exp hSmall α hα.le
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = C1 * max k 3 ^ 2 := ⟨_, rfl⟩
  refine ⟨q * (2 * (A + C2 + 5 * k) + 2) * c₁, fun n φ hn hφ => ?_⟩
  obtain ⟨hw3, hwk, hwle⟩ := hW n φ
  have hwmax := (hwle k hk hφ).1
  have hE := expVariables_pos α hn
  have hX : (SatM.enc k φ).length + 1 ≤ (n + 2) ^ (A + C2 + 5 * k) :=
    (UniformInK.Time.length_enc_succ_le hk hφ).trans (Nat.pow_le_pow_right (by omega) (by omega))
  by_cases ht : test (SatM.enc k φ) = true
  · obtain ⟨hK, hw4⟩ := (htest k n φ hk hφ).1 ht
    have hrun : Outputs M (SatM.enc (widthOr3 φ) φ) (SatK.binary n (SatK.numSat φ)) (timeVariablesAAlpha C1 (widthOr3 φ) n α) := h1 (widthOr3 φ) n φ hK hw3 hw4 (hwk hφ.2)
    rw [← hpre k n φ hk hφ] at hrun
    have hle : C1 * widthOr3 φ ^ 2 ≤ A + C2 + 5 * k := by
      have : C1 * widthOr3 φ ^ 2 ≤ A := by rw [hA]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwmax 2)
      omega
    exact Outputs.mono ((hN _ _ _).1 ht hrun) (absorb α hc₁ hB q _ hn ((timeVariablesAAlpha_le C1 _ n α).trans (two_rpow_mono hle hE.le)) hX)
  · have ht' : test (SatM.enc k φ) = false := by simpa using ht
    have hlt : n < n₀ := by
      by_contra hge
      obtain ⟨a1, a2⟩ := hn₀ n (not_lt.1 hge)
      exact ht ((htest k n φ hk hφ).2 ⟨a1, le_trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hwmax) 4) a2⟩)
    have hrun : Outputs Mb (SatM.enc k φ) (SatK.binary n (SatK.numSat φ)) (2 ^ (c * n) * n ^ (c * k)) := hMb k n φ hk (by omega) hφ
    have hle : ((2 ^ (c * n) * n ^ (c * k) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((A + C2 + 5 * k : ℕ) : ℝ) * expVariables α n) :=
      le_trans (le_trans (Nat.cast_le.2 (h2 n hn hlt)) (timeVariables_le α C2 n)) (two_rpow_mono (by omega) hE.le)
    exact Outputs.mono ((hN _ _ _).2 ht' hrun) (absorb α hc₁ hB q _ hn hle hX)
end FixedWidthSteps
