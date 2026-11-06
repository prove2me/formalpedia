-- Prove2me | solution 1 for ExplicitCost.lbLen_groupingInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:28:18.72605+00:00
-- url     : https://prove2.me/submissions/240b1873-f536-4936-ba5f-1cf8b345e1d5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Eight_ViaGrouping_Search
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingNumbers
import Theorems.Thm_Eight_ViaGrouping_Table_lbLen_eq_Y
import Theorems.Thm_Eight_ViaGrouping_lbLen_eq_Y
import Theorems.Thm_Printed_asked_isNetworkP


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (a b K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ)
variable {P B}
namespace ExplicitCost
theorem _root_.solution (hK0 : 0 < K) (hN : N.Is P B) (x : ℕ) {γ γ' : Fin K} (hne : γ ≠ γ') :
    lbLen K g askedData.under.toPaperNetwork (groupingInput a b K N P B).2 x γ.val γ'.val = Y N.c (Paper.grouping hK0 x) γ γ' :=
  lbLen_eq_Y hK0 (asked_isNetworkP N hN) x hne
end ExplicitCost
