-- Prove2me | solution 2 for CircuitLowerBound.Round.nu_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:43:38.549767+00:00
-- url     : https://prove2.me/submissions/5d319809-780c-4795-bb19-ac291af3fccd

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
import Theorems.Thm_CircuitLowerBound_Round_length_bits_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Sat3_Is3CNF_length_le


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round
namespace CircuitLowerBound.Round
theorem _root_.solution (m : ℕ) : nu m ≤ m := by
  rw [nu]
  exact (List.takeWhile_sublist _).length_le.trans (length_bits_le m)
end CircuitLowerBound.Round
