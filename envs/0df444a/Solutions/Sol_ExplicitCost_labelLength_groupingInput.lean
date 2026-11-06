-- Prove2me | solution 1 for ExplicitCost.labelLength_groupingInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:42:46.673466+00:00
-- url     : https://prove2.me/submissions/ba8ffad4-2035-47ce-bc11-a91771c7bfce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Eight_ViaGrouping_Search
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingNumbers
import Theorems.Thm_ExplicitCost_inK_groupingInput
import Theorems.Thm_ExplicitCost_inG_groupingInput
import Theorems.Thm_ExplicitCost_inP_groupingInput
import Theorems.Thm_ExplicitCost_inU_groupingInput

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (a b K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ)
variable {P B}
namespace ExplicitCost
theorem _root_.solution (hN : N.Is P B) :
    labelLength (groupingInput a b K N P B) = (b * N.U + 2 * min a b * g * P + b * K ^ 2 - 1) / (b * K ^ 2) := by
  unfold labelLength
  rw [inU_groupingInput a b K N hN, inG_groupingInput, inP_groupingInput, inK_groupingInput]
  rfl
end ExplicitCost
