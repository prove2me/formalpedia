-- Prove2me | solution 1 for ExplicitCost.size_value_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:43:17.684336+00:00
-- url     : https://prove2.me/submissions/4ed8b7c8-a657-41b2-a979-425bc8256374

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_GroupingSearch
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_GroupingRun
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Value_End
import Definitions.Def_GeneralPieces_Main
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingCall
import Theorems.Thm_ExplicitCost_abs_value_le
import Theorems.Thm_ClauseBound_Alg_Level_abs_value_le
import Theorems.Thm_Groundwork_Prog_abs_value_le
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_PaddedDescent_F_Arith_size_le
import Theorems.Thm_PaddedDescent_F_Mark_InvS_size
attribute [local simp] Groundwork.size_int



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {g : ℕ} {N : Net g} {P B : ℕ} (h : N.Is P B) : size N.value ≤ g * P + g * B + g ^ 2 * B + 2 := by
  rw [size_int]
  refine Nat.succ_le_succ (Nat.size_le.2 ?_)
  have h1 : (N.value.natAbs : ℤ) ≤ 2 ^ (g * P + g * B + g ^ 2 * B) := by
    rw [Int.natCast_natAbs]
    exact abs_value_le h
  have h2 : N.value.natAbs ≤ 2 ^ (g * P + g * B + g ^ 2 * B) := by exact_mod_cast h1
  exact h2.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
end ExplicitCost
