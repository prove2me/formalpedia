-- Prove2me | solution 1 for CircuitLowerBound.Round.mL_roundInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:55:45.439445+00:00
-- url     : https://prove2.me/submissions/959fdbd7-2dd0-4a50-8575-fe0de5f083f6

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
import Theorems.Thm_CircuitLowerBound_Round_length_roundInput
import Theorems.Thm_CircuitLowerBound_Round_getD_even
import Theorems.Thm_CircuitLowerBound_Round_getD_end
import Theorems.Thm_CircuitLowerBound_Round_takeWhile_range
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round
namespace CircuitLowerBound.Round
theorem _root_.solution (x ans : List Bool) : mL (roundInput x ans) = List.range x.length :=
  takeWhile_range (fun i hi => getD_even x ans i hi) (getD_end x ans) (by rw [length_roundInput]; omega)
end CircuitLowerBound.Round
