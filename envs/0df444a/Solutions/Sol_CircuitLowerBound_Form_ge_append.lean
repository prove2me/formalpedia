-- Prove2me | solution 1 for CircuitLowerBound.Form.ge_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:50:58.129267+00:00
-- url     : https://prove2.me/submissions/1622bc2c-bfc5-4444-9513-abb3e5af7cc3

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
import Theorems.Thm_CircuitLowerBound_Form_forall_append
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Form
namespace CircuitLowerBound.Form
theorem _root_.solution (a : ℕ → Bool) (N : ℕ) (A B : List GateD) : GE a N (A ++ B) ↔ GE a N A ∧ GE a (N + A.length) B :=
  forall_append (fun i g => a i = g.toGate.op (a g.2.1) (a g.2.2)) N A B
end CircuitLowerBound.Form
