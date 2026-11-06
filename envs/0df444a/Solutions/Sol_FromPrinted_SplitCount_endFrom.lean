-- Prove2me | solution 1 for FromPrinted.SplitCount.endFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:29:30.024602+00:00
-- url     : https://prove2.me/submissions/390d2dfb-96c4-474e-8e71-fc5ecd01b26a

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
import Theorems.Thm_CountKSat_EndLemmas_not_CountETH_TM_of
import Theorems.Thm_Eight_ViaGrouping_Cost_floor_le


set_option autoImplicit false
section
section
open SplitCount
open FromPrinted FromPrinted.SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal
namespace FromPrinted.SplitCount
theorem _root_.solution (h : StTiedTM) : ThreeSatStatement := by
  refine ⟨fun k hk δ hδ => ?_, EndLemmas.not_CountETH_TM_of fun δ hδ => ?_⟩
  · obtain ⟨ℓ, τ, M, c, q, hfin, -, -, -, hM⟩ := h k (by omega) δ hδ
    exact ⟨c, M, _, hfin, hM, fun n _ => Nat.floor_le (by positivity)⟩
  · obtain ⟨ℓ, τ, M, c, q, hfin, -, -, -, hM⟩ := h 3 (by norm_num) (δ : ℝ) (NNReal.coe_pos.2 hδ)
    exact ⟨M, c, hfin, hM⟩
end FromPrinted.SplitCount
