-- Prove2me | solution 1 for CircuitLowerBound.Form.not_all_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:56:01.360275+00:00
-- url     : https://prove2.me/submissions/9cd02b00-ccb1-473f-8411-9e9e1ad31418

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
theorem _root_.solution (e : MCode) (L P : ℕ) (f : ℕ → Bool) :
    (¬∀ D ∈ tabF e L P, ∃ l ∈ D, f l.1 = l.2) ↔ ∃ j < 2 ^ nb e L, ∀ l ∈ clauseAt e L P j, f l.1 ≠ l.2 := by
  constructor
  · intro h
    by_contra hc
    refine h fun D hD => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hD
    by_contra h2
    exact hc ⟨j, List.mem_range.1 hj, fun l hl he => h2 ⟨l, hl, he⟩⟩
  · rintro ⟨j, hj, hv⟩ H
    obtain ⟨l, hl, he⟩ := H _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
    exact hv l hl he
end CircuitLowerBound.Form
