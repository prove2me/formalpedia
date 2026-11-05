-- Prove2me | solution 1 for CircuitLowerBound.Round.xW_polyT
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T00:27:44.143104+00:00
-- url     : https://prove2.me/submissions/891cabaf-f8ff-4590-b578-951e41bb2ace

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

attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.takeWhile

theorem solution : PolyT xW := by
  have := CircuitLowerBound.Round.mL_polyT
  unfold CircuitLowerBound.xW
  fun_prop
