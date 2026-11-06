-- Prove2me | solution 1 for ExplicitCost.Sizes.size_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:17:25.183928+00:00
-- url     : https://prove2.me/submissions/ee1f77b1-bf02-488b-a995-95a015641001

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
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_PaddedDescent_F_Arith_size_le
import Theorems.Thm_PaddedDescent_F_Mark_InvS_size
attribute [local simp] Groundwork.size_nat



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
open ExplicitCost.Sizes
namespace ExplicitCost.Sizes
theorem _root_.solution {K g : ℕ} (hKg : K ≤ g) : size (K ^ g) ≤ g * g + 2 := by
  rw [size_nat]
  refine Nat.succ_le_succ (Nat.size_le.2 ?_)
  calc K ^ g ≤ (2 ^ g) ^ g := Nat.pow_le_pow_left (hKg.trans Nat.lt_two_pow_self.le) g
    _ = 2 ^ (g * g) := (pow_mul 2 g g).symm
    _ < 2 ^ (g * g + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
end ExplicitCost.Sizes
