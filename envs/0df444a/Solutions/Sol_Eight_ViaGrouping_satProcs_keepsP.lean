-- Prove2me | solution 1 for Eight.ViaGrouping.satProcs_keepsP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:57:49.705196+00:00
-- url     : https://prove2.me/submissions/8a1215ad-23cc-4b09-9cae-f9cc778b02de

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_SatPsiDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_ToTuring_Poly_Count
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Theorems.Thm_Eight_ViaGrouping_satPsiM_isPolyT
import Theorems.Thm_Eight_ViaGrouping_satPf_unary
import Theorems.Thm_Eight_ViaGrouping_keepsP_ofProcs
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Prog_satP_keeps
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight.SecNetworks
variable {g k : ℕ} {Φ : Fml}
namespace Eight.ViaGrouping
theorem _root_.solution (g k : ℕ) : KeepsP (satProcs g k) := keepsP_ofProcs (satP_keeps g k) (satPf_unary g k) (satPsiM_isPolyT g k)
end Eight.ViaGrouping
