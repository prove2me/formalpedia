-- Prove2me | solution 1 for ExplicitCost.searchFinds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:28:05.897891+00:00
-- url     : https://prove2.me/submissions/5ec9f8d3-34bb-4b13-91f7-0e61160991cc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_GroupingNumbers
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_Exits_Runs
import Definitions.Def_Exits_Tested
import Definitions.Def_Eight_ViaGrouping_Search
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingSearch
import Theorems.Thm_ExplicitCost_goodData_iff
import Theorems.Thm_AppRunningTime_someGrouping
import Theorems.Thm_Eight_ViaGrouping_grouping_number
import Theorems.Thm_GeneralPieces_someGrouping
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution : SearchFinds := by
  intro a b K g hK0 N P B hK hg ha hab hN hC
  have hb : 0 < b := by omega
  have hζ0 : (0 : ℝ) < (a : ℝ) / b := div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hζ1 : (a : ℝ) / b ≤ 1 := (div_le_one (by exact_mod_cast hb)).2 (by exact_mod_cast hab)
  obtain ⟨χ, h1, h2⟩ := AppRunningTime.someGrouping K g _ P N.c hK hg hζ0 hζ1 hN.P_pos hN.c_symm hN.i hC
  obtain ⟨x', hx', rfl⟩ := grouping_number hK0 χ
  have hgood' : goodData (groupingInput a b K N P B, x') = true := (goodData_iff hK0 hb hab hN x').2 ⟨h1, h2⟩
  obtain ⟨x, hfind⟩ : ∃ x, (List.range (K ^ g)).find? (fun y => goodData (groupingInput a b K N P B, y)) = some x := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨x', List.mem_range.2 hx', hgood'⟩
  have hgood : goodData (groupingInput a b K N P B, x) = true := List.find?_some (p := fun y => goodData (groupingInput a b K N P B, y)) hfind
  obtain ⟨g1, g2⟩ := (goodData_iff hK0 hb hab hN x).1 hgood
  exact ⟨x, List.mem_range.1 (List.mem_of_find?_eq_some hfind), hfind, g1, g2⟩
end ExplicitCost
