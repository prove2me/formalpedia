-- Prove2me | solution 1 for CircuitLowerBound.Round.eW_polyT
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:05:54.478147+00:00
-- url     : https://prove2.me/submissions/1c4381c4-aaaf-4a0e-8f7f-45c84c98c9b5

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
import Theorems.Thm_CircuitLowerBound_Round_mL_polyT
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round
variable {G : (MCode × List Unit × ℕ) × List Unit → Cnf} {fb : List Unit → Bool}
variable {α : Type} [Enc α]

attribute [local fun_prop] Groundwork.PolyT.length Groundwork.PolyT.mul Groundwork.PolyT.const

theorem solution : PolyT eW := by
  have := mL_polyT
  unfold eW
  fun_prop
