-- Prove2me | solution 1 for CircuitLowerBound.Round.drop_roundInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:43:27.044486+00:00
-- url     : https://prove2.me/submissions/050bb0fe-5e9d-44eb-b95c-6298051a5651

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
import Theorems.Thm_CircuitLowerBound_Round_roundInput_cons
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round
namespace CircuitLowerBound.Round
theorem _root_.solution (x ans : List Bool) : (roundInput x ans).drop (2 * x.length + 1) = ans := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    rw [roundInput_cons, List.length_cons, show 2 * (x.length + 1) + 1 = 2 * x.length + 1 + 1 + 1 by ring, List.drop_succ_cons, List.drop_succ_cons]
    exact ih
end CircuitLowerBound.Round
