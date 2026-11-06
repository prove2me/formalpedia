-- Prove2me | solution 1 for CircuitLowerBound.Clause.dq_le_dSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:50:10.318327+00:00
-- url     : https://prove2.me/submissions/1ebe6100-842b-4916-88d8-b5d7f1e29978

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Clause_litI_zeroCl
import Theorems.Thm_CircuitLowerBound_Clause_le_sum_map
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
namespace CircuitLowerBound.Clause
theorem _root_.solution (tb : List TCl) (k ι : ℕ) : (litI (tb.getD k zeroCl) ι).2.2.2.1 ≤ dSum tb := by
  by_cases hk : k < tb.length
  · rw [List.getD_eq_getElem _ _ hk]
    refine le_trans ?_ (le_sum_map (fun c : TCl => c.1.2.2.2.1 + c.2.1.2.2.2.1 + c.2.2.2.2.2.1) tb (List.getElem_mem hk))
    unfold litI
    split_ifs <;> omega
  · rw [List.getD_eq_default _ _ (by omega), litI_zeroCl]
    exact Nat.zero_le _
end CircuitLowerBound.Clause
