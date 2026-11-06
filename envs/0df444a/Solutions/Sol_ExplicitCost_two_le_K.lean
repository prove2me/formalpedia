-- Prove2me | solution 1 for ExplicitCost.two_le_K
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:56:15.782841+00:00
-- url     : https://prove2.me/submissions/38e47370-6fa9-4f9d-84ef-b8d38171a01b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_SolverStages
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverPattern
import Theorems.Thm_ExplicitCost_two_pow_le_K


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {x₀ : ℕ} (hx : 1 ≤ x₀) (l : ℕ) : 2 ≤ Levels.Gen.K x₀ l :=
  le_trans (by calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ x₀ := Nat.pow_le_pow_right (by norm_num) hx) (two_pow_le_K x₀ l)
end ExplicitCost
