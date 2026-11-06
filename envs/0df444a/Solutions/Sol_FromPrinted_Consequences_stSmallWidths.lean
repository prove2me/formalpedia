-- Prove2me | solution 1 for FromPrinted.Consequences.stSmallWidths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:16:32.766135+00:00
-- url     : https://prove2.me/submissions/b1fefead-f9bb-462a-9dfb-78bbfac789ec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_FromPrinted_SplitSat
import Definitions.Def_Eight_ViaGrouping_CorNSETH
import Definitions.Def_CountKSat_InOut
import Definitions.Def_WidthK_Decode
import Definitions.Def_FromPrinted_Verifier
import Theorems.Thm_ClauseBound_Alg_End_length_enc
import Theorems.Thm_CountKSat_stCertDecU
import Theorems.Thm_CountKSat_stDecU
import Theorems.Thm_FromPrinted_SplitSat_stCore3
import Theorems.Thm_Groundwork_DecodeK_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_Decode_mem_toN
import Theorems.Thm_Groundwork_Decode_satN_toN
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_SatTopK_length_enc
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
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
import Theorems.Thm_SplitSat_stCore3
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog CountKSat Paper Eight Eight.ViaGrouping
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement
open FromPrinted.SplitSat
open FromPrinted FromPrinted.Consequences
namespace FromPrinted.Consequences
theorem _root_.solution : StSmallWidths := by
  intro k hk hk3 δ hδ
  obtain ⟨ℓ, τ, ⟨hI⟩, c, hc⟩ := FromPrinted.SplitSat.stCore3 δ hδ
  refine ⟨ℓ, τ, c, ⟨IsPolyT.mapIn (M := core3 ℓ τ) (stCertDecU k)⟩, fun n φ h3 => ?_⟩
  have hw : ∀ C ∈ Decode.toN φ, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n := by
    intro C hC
    obtain ⟨⟨D, hD, hl⟩, h⟩ := Decode.mem_toN hC
    exact ⟨hl ▸ (h3.1 D hD).trans hk3, h⟩
  have hnd : (Decode.toN φ).Nodup := by
    refine List.Nodup.map (List.map_injective_iff.2 fun a b hab => ?_) h3.2
    exact Prod.ext (Fin.ext (Prod.ext_iff.1 hab).1) (Prod.ext_iff.1 hab).2
  obtain ⟨T, b, r, hb, hT⟩ := hc n (Decode.toN φ) hw hnd
  refine ⟨T, b, (Stepped.mapIn_runs (by rw [stDecU k n φ hk h3.1]; exact r)).mono le_rfl ?_, hb.trans (Decode.satN_toN φ), hT⟩
  have hlen := DecodeK.length_enc k φ
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c)
end FromPrinted.Consequences
