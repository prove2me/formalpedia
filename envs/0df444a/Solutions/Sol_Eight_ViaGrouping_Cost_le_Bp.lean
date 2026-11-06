-- Prove2me | solution 1 for Eight.ViaGrouping.Cost.le_Bp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:28:20.830356+00:00
-- url     : https://prove2.me/submissions/d2cdace2-b422-47a7-8769-58ba58d953ee

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
import Theorems.Thm_Eight_ViaGrouping_Cost_floor_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Cost
namespace Eight.ViaGrouping.Cost
theorem _root_.solution (K g P B : ℕ) : P * (2 * g / K) + g ^ 2 * B ≤ Bp K g P B :=
  Nat.add_le_add_right (Nat.cast_le.1 ((floor_le K g P).trans (Nat.le_ceil _))) _
end Eight.ViaGrouping.Cost
