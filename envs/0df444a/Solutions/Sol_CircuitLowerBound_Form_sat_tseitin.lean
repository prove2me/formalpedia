-- Prove2me | solution 1 for CircuitLowerBound.Form.sat_tseitin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:03:07.194752+00:00
-- url     : https://prove2.me/submissions/f2732c7b-bbaa-47da-8b65-dbecd5129971

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
import Theorems.Thm_CircuitLowerBound_Form_sat_gateCl

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Form
namespace CircuitLowerBound.Form
theorem _root_.solution (a : ℕ → Bool) (n : ℕ) (K : List GateD) : (∀ D ∈ tseitin n K, ∃ l ∈ D, a l.1 = l.2) ↔ GE a n K := by
  unfold tseitin GE
  constructor
  · intro H t h
    rw [← sat_gateCl]
    intro D hD
    exact H D (List.mem_flatMap.2 ⟨t, List.mem_range.2 h, by rwa [List.getD_eq_getElem _ _ h]⟩)
  · intro H D hD
    obtain ⟨t, ht, hD⟩ := List.mem_flatMap.1 hD
    have h := List.mem_range.1 ht
    rw [List.getD_eq_getElem _ _ h] at hD
    exact (sat_gateCl a _ _).2 (H t h) D hD
end CircuitLowerBound.Form
