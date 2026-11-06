-- Prove2me | solution 1 for CircuitLowerBound.Form.nF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:56:03.381944+00:00
-- url     : https://prove2.me/submissions/287aed9f-a1a1-427a-bf81-677731cd01a9

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
theorem _root_.solution {e : MCode} {L P : ℕ} (h : Fits e L P) : nF e L = nb e L := by
  obtain ⟨h1, -⟩ := h
  have h2 : 2 * ((L - kb e - lam e - 2) / 2) ≤ L - kb e - lam e - 2 := Nat.mul_div_le _ 2
  unfold nF nb bq bt
  exact min_eq_left (by omega)
end CircuitLowerBound.Form
