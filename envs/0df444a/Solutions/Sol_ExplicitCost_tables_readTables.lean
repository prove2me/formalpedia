-- Prove2me | solution 1 for ExplicitCost.tables_readTables
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:44:27.701613+00:00
-- url     : https://prove2.me/submissions/11271e2d-dbd9-41d6-bc64-8db93e62552e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_Brute
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Base
import Theorems.Thm_ExplicitCost_readTables_setting
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (K lam : ℕ) (W : ℕ → List Bool → ℤ) : tables K lam (readTables (answersOf K lam W)) = tables K lam W := by
  funext q
  by_cases h : q.1 < K ∧ q.2.length = (K - 1) * lam
  · exact (if_pos h).trans ((congrArg some (readTables_setting W h.1 h.2)).trans (if_pos h).symm)
  · exact (if_neg h).trans (if_neg h).symm
end ExplicitCost
