-- Prove2me | solution 1 for CircuitLowerBound.Form.xor_op
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:53:32.873747+00:00
-- url     : https://prove2.me/submissions/38cf237f-7586-4c37-a5fa-1489fe756507

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Form

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Form
namespace CircuitLowerBound.Form
theorem _root_.solution (i j : ℕ) (x y : Bool) : (GateD.toGate (xorT, i, j)).op x y = (x != y) := by
  cases x <;> cases y <;> rfl
end CircuitLowerBound.Form
