-- Prove2me | solution 1 for FreeCode.stBehindReader
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:22:03.350123+00:00
-- url     : https://prove2.me/submissions/5347476c-7f30-4916-b160-8d22be8497ef

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_FreeCode_Behind
import Theorems.Thm_Groundwork_Decode_mem_toN
import Theorems.Thm_Groundwork_Decode_satN_toN
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SplitSat_nodup_toN


set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Paper SplitSat
namespace FreeCode
theorem _root_.solution : StBehindReader := fun dec hdec w D δ c h n φ h3 => by
  obtain ⟨T, b, r, hb, hT⟩ := h n (Decode.toN φ) (fun E hE => by
    obtain ⟨⟨C, hC, hl⟩, h'⟩ := Decode.mem_toN hE
    exact ⟨hl ▸ h3.1 C hC, h'⟩) (nodup_toN h3.2)
  refine ⟨T, b, Stepped.mapIn_runs ?_, hb.trans (Decode.satN_toN φ), hT⟩
  rw [hdec n φ]
  exact r
end FreeCode
