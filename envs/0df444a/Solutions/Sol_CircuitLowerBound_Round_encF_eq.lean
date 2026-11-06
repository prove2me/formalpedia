-- Prove2me | solution 1 for CircuitLowerBound.Round.encF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:43:49.087281+00:00
-- url     : https://prove2.me/submissions/484cd712-7784-4e8e-9bba-1f779d6f763b

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
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round
namespace CircuitLowerBound.Round
theorem _root_.solution {pad : List Unit} {φ : Cnf} (h : ∀ C ∈ φ, ∀ l ∈ C, l.1 ≤ pad.length) : encF pad φ = encCnf φ := by
  unfold encF encCnf
  congr 1
  refine List.flatMap_congr fun C hC => ?_
  congr 1
  refine List.flatMap_congr fun l hl => ?_
  rw [encLit, List.map_const', List.length_take, Nat.min_eq_left (h C hC l hl)]
end CircuitLowerBound.Round
