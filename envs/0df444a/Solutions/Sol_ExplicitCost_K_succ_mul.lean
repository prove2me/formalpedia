-- Prove2me | solution 1 for ExplicitCost.K_succ_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:56:29.698229+00:00
-- url     : https://prove2.me/submissions/2ceb94f5-1c3a-4348-b860-b71450e45825

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_SolverStages
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverPattern

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (x₀ l : ℕ) : Levels.Gen.K x₀ (l + 1) = Levels.Gen.g x₀ l * Levels.Gen.g x₀ l := by
  show (2 ^ (3 * l + x₀) * Levels.Gen.K x₀ l) ^ 2 = _
  rw [sq]
  rfl
end ExplicitCost
