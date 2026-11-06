-- Prove2me | solution 1 for ExplicitCost.clique_readTables
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:27:21.827765+00:00
-- url     : https://prove2.me/submissions/4fd4b59b-1d07-4550-ac31-c257b50a30e7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Definitions.Def_ClauseBound_Alg_Level
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CliqueReads
import Theorems.Thm_ExplicitCost_clique_value_congr
import Theorems.Thm_ExplicitCost_readTables_setting
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (K lam : ℕ) (W : ℕ → List Bool → ℤ) : (clique K lam fun w => readTables (answersOf K lam W) w.val).value = (clique K lam fun w => W w.val).value :=
  clique_value_congr fun w _ hz => readTables_setting W w.2 (mem_words.1 hz)
end ExplicitCost
