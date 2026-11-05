-- Prove2me | solution 1 for Eight.network_exponent_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:51:38.548818+00:00
-- url     : https://prove2.me/submissions/734efe71-6be4-4d2c-b19d-755483573f8a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecProof_NetworkDefs
import Definitions.Def_SingleBitPieces_SecProof_Cost
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_SecProof_Network
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_SingleBitPieces_network_exponent_le
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
namespace Eight
theorem _root_.solution {δ' : ℝ} {K U g P m : ℕ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hK : 72 / δ' ≤ K) (hU : U < 6 * m) (hP : g * P ≤ 6 * (m + g)) :
    δ' / 12 * ((U : ℝ) + (g : ℝ) * P / K) + 2 * (g : ℝ) * P / K < 97 / 144 * δ' * m + 25 / 144 * δ' * g := by
  have h := SingleBitPieces.network_exponent_le (U := U + 1) hδ' h1 hK hU hP
  push_cast at h
  nlinarith
end Eight
