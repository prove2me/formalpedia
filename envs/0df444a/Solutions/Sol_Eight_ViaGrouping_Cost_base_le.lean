-- Prove2me | solution 1 for Eight.ViaGrouping.Cost.base_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:54:00.183057+00:00
-- url     : https://prove2.me/submissions/b32b1e3d-09cd-4dc9-848d-e390b8d456b5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
import Theorems.Thm_Eight_ViaGrouping_Cost_Bp_le
import Theorems.Thm_Eight_SecNetworks_L_le


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Cost
namespace Eight.ViaGrouping.Cost
theorem _root_.solution {K g : ℕ} (U P B : ℕ) (hK : 1 ≤ K) (hg : 1 ≤ g) (hP : 1 ≤ P) (hU : U ≤ g * P) :
    Bp K g P B + Paper.groupedLength K g U P ≤ (4 * g + g ^ 2) * (P + B) := by
  have h1 := Bp_le g P B hK
  have h2 := L_le hK hg hP hU
  have e : (4 * g + g ^ 2) * (P + B) = (2 * g + g ^ 2) * (P + B) + 2 * (g * P) + 2 * (g * B) := by ring
  omega
end Eight.ViaGrouping.Cost
