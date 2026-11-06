-- Prove2me | solution 1 for ExplicitCost.inU_groupingInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:28:17.652819+00:00
-- url     : https://prove2.me/submissions/fc8c1350-8815-4722-b224-153f80f27562

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Eight_ViaGrouping_Search
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingNumbers
import Theorems.Thm_ExplicitCost_inG_groupingInput
import Theorems.Thm_Eight_ViaGrouping_Uc_eq_U
import Theorems.Thm_Printed_asked_isNetworkP


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (a b K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ)
variable {P B}
namespace ExplicitCost
theorem _root_.solution (hN : N.Is P B) : inU (groupingInput a b K N P B) = N.U := by
  unfold inU
  rw [inG_groupingInput]
  have h := Uc_eq_U (asked_isNetworkP N hN)
  exact h
end ExplicitCost
