-- Prove2me | solution 1 for Eight.ViaGrouping.count_isPolyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:06:58.376004+00:00
-- url     : https://prove2.me/submissions/e34f2ba5-b584-46a4-85d8-c67b53df86c0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Eight_SecProof_Proof
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Count
import Theorems.Thm_Eight_ViaGrouping_satProcs_keepsP
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Paper
namespace Eight.ViaGrouping
theorem _root_.solution {NA : NetAlg} (h : AlgKeeps NA) (g k : ℕ) : Nonempty (IsPolyT (NA.app (satProcs g k))) := h Fml (satProcs g k) (satProcs_keepsP g k)
end Eight.ViaGrouping
