-- Prove2me | solution 1 for ExplicitCost.Sizes.search_sizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:41:50.062439+00:00
-- url     : https://prove2.me/submissions/b1d89387-54f9-4c3b-aafa-d492ba89ca8d

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
import Theorems.Thm_ExplicitCost_Sizes_basic_facts
import Theorems.Thm_ExplicitCost_Sizes_sq_le_pow


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
open ExplicitCost.Sizes
namespace ExplicitCost.Sizes
theorem _root_.solution {K g P B s sc sk : ℕ} (hK0 : 0 < K) (hKg : K ≤ g) (hP : 1 ≤ P) (hB : 1 ≤ B) (hsc : sc ≤ (4 * g ^ 2 + 6 * g + 6) * (P + B)) (hsk : sk ≤ g * g + 2) :
    4 * (s + (2 * K + 2 * g + 2 + sc)) + 4 * sk + 40 ≤ (g * (P + B) + s) ^ 10 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := basic_facts (hK0.trans_le hKg) hP hB
  refine le_trans ?_ (sq_le_pow (X := g * (P + B) + s) (by omega))
  have s1 : sc ≤ 4 * (g * g * (P + B)) + 6 * (g * (P + B)) + 6 * (P + B) := by
    have : (4 * g ^ 2 + 6 * g + 6) * (P + B) = 4 * (g * g * (P + B)) + 6 * (g * (P + B)) + 6 * (P + B) := by ring
    omega
  have e : (g * (P + B) + s) * (g * (P + B) + s) = g * (P + B) * (g * (P + B)) + 2 * (g * (P + B) * s) + s * s := by ring
  have s2 : 2 * s ≤ g * (P + B) * s := Nat.mul_le_mul_right _ (by omega)
  have s3 : 4 ≤ g * (P + B) * (g * (P + B)) := by
    have : 2 * 2 ≤ g * (P + B) * (g * (P + B)) := Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [e]
  omega
end ExplicitCost.Sizes
