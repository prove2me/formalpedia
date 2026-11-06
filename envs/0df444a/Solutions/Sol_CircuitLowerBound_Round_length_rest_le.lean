-- Prove2me | solution 1 for CircuitLowerBound.Round.length_rest_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:43:37.433219+00:00
-- url     : https://prove2.me/submissions/6b62e89a-67df-4ca2-9e5c-3828031213de

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Round
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Sat3_Is3CNF_length_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round
namespace CircuitLowerBound.Round
theorem _root_.solution (x : List Bool) : (rest x).length ≤ x.length := by
  rw [rest, List.length_tail]
  exact (Nat.sub_le _ _).trans (List.dropWhile_sublist _).length_le
end CircuitLowerBound.Round
