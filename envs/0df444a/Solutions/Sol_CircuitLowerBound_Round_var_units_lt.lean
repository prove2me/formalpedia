-- Prove2me | solution 1 for CircuitLowerBound.Round.var_units_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:50:52.994591+00:00
-- url     : https://prove2.me/submissions/79ef3f67-be48-43a8-a2ae-cc65548c7a6a

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
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round
namespace CircuitLowerBound.Round
theorem _root_.solution (w : List Bool) : ∀ C ∈ units w, ∀ l ∈ C, l.1 < w.length := by
  intro C hC l hl
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hC
  rw [List.mem_singleton.1 hl]
  exact List.mem_range.1 hi
end CircuitLowerBound.Round
