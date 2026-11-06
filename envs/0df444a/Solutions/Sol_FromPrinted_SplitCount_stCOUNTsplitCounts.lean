-- Prove2me | solution 1 for FromPrinted.SplitCount.stCOUNTsplitCounts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:05:32.010569+00:00
-- url     : https://prove2.me/submissions/35ae4c9a-4a12-4539-bd35-e9eafc0470b9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_CountDefs
import Definitions.Def_Printed_End
import Definitions.Def_SplitCount_StepOne
import Definitions.Def_SplitCount_Main
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Suffices
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Count
import Theorems.Thm_FromPrinted_SplitCount_stEngineCounts
import Theorems.Thm_ClauseBound_Alg_End_length_enc
import Theorems.Thm_CountKSat_EndLemmas_CountsTM_mono
import Theorems.Thm_CountKSat_stCertDecU
import Theorems.Thm_CountKSat_stCntToN
import Theorems.Thm_CountKSat_stDecU
import Theorems.Thm_Groundwork_DecodeK_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_Decode_mem_toN
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_SatTopK_length_enc
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open SplitCount
open FromPrinted FromPrinted.SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal
namespace FromPrinted.SplitCount
theorem _root_.solution : StCOUNTsplitCounts := by
  intro k hk δ hδ
  obtain ⟨ℓ, τ, ⟨hI⟩, c, hS⟩ := stEngineCounts k hk δ hδ
  refine ⟨ℓ, τ, ?_, c, fun n φ h3 => ?_⟩
  · have := hI
    exact ⟨IsPolyT.mapIn (M := ENGINEsplit k ℓ τ) (stCertDecU k)⟩
  · have hc : ∀ C ∈ Decode.toN φ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
      intro C hC
      obtain ⟨⟨D, hD, hl⟩, h⟩ := Decode.mem_toN hC
      exact ⟨hl ▸ h3.1 D hD, h⟩
    have hnd : (Decode.toN φ).Nodup := by
      refine List.Nodup.map (List.map_injective_iff.2 fun a b hab => ?_) h3.2
      exact Prod.ext (Fin.ext (Prod.ext_iff.1 hab).1) (Prod.ext_iff.1 hab).2
    obtain ⟨T, r, hT⟩ := hS n (Decode.toN φ) hc hnd
    rw [stCntToN] at r
    refine ⟨T, (Stepped.mapIn_runs (by rw [stDecU k n φ hk h3.1]; exact r)).mono le_rfl ?_, hT⟩
    have hlen := DecodeK.length_enc k φ
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c)
end FromPrinted.SplitCount
