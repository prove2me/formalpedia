-- Prove2me | solution 1 for Eight.decidesInSteps_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:15:09.617566+00:00
-- url     : https://prove2.me/submissions/9ce689b9-10f0-4d43-b0ac-664b4dc9a318

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
theorem _root_.solution {Ms : StepMachine (List Bool) Bool} {δ δ₁ : ℝ} (h : Paper.DecidesInSteps Ms δ) (hle : δ ≤ δ₁) : Paper.DecidesInSteps Ms δ₁ := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun n φ hφ => ?_⟩
  obtain ⟨T, b, h1, h2, h3⟩ := hc n φ hφ
  refine ⟨T, b, h1, h2, h3.trans ?_⟩
  gcongr
  norm_num
end Eight
