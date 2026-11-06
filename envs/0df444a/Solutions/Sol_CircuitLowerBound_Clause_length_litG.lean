-- Prove2me | solution 1 for CircuitLowerBound.Clause.length_litG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:40:49.387141+00:00
-- url     : https://prove2.me/submissions/6e28bba9-688a-4f08-bdbc-d4e8fb8dceb9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Clause_length_timeG
import Theorems.Thm_CircuitLowerBound_Clause_length_posG
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
namespace CircuitLowerBound.Clause
theorem _root_.solution (n bq bt rb R kbm Dq P ι : ℕ) : (litG n bq bt rb R kbm Dq P ι).length = szL bq bt := by
  rw [litG, List.length_append, length_timeG, length_posG, szL]
  omega
end CircuitLowerBound.Clause
