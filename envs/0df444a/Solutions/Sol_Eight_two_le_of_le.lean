-- Prove2me | solution 1 for Eight.two_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:14:05.915422+00:00
-- url     : https://prove2.me/submissions/368e5124-027f-4678-a344-8c56ba8171bd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_End
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_CountKSat_Value
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_Eight_SecProof_Proof
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog Paper
namespace Eight
theorem _root_.solution {δ' : ℝ} {K : ℕ} (hδ' : 0 < δ') (h3 : δ' ≤ 1 / 3) (hK : 72 / δ' ≤ K) : 2 ≤ K := by
  have h1 : (2 : ℝ) ≤ 72 / δ' := by rw [le_div_iff₀ hδ']; linarith
  exact_mod_cast h1.trans hK
end Eight
