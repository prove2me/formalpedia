-- Prove2me | solution 1 for Eight.ViaGrouping.satPf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:19:40.632443+00:00
-- url     : https://prove2.me/submissions/ae8983ae-33ea-4298-ab26-78a876e67fdf

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
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Paper
namespace Eight.ViaGrouping
theorem _root_.solution (g k : ℕ) (Φ : Fml) : satPf g k Φ ≤ 2 * (mu g Φ * k) + 1 := by
  have : 2 * k * mu g Φ = 2 * (mu g Φ * k) := by ring
  unfold satPf
  omega
end Eight.ViaGrouping
