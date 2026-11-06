-- Prove2me | solution 1 for CircuitLowerBound.Round.nb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:58:41.287837+00:00
-- url     : https://prove2.me/submissions/5f1038e0-04f9-43c2-b44f-f3bb57200693

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
import Theorems.Thm_CircuitLowerBound_Round_length_tab_codeOf_le
import Theorems.Thm_CircuitLowerBound_Round_nu_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round
namespace CircuitLowerBound.Round
theorem _root_.solution {m P : ℕ} (h : Fits (codeOf (nu m)) m P) : nb (codeOf (nu m)) m ≤ 2 * m := by
  have h1 : rb (codeOf (nu m)) ≤ m := by
    rw [rb]
    exact (Nat.size_le.2 Nat.lt_two_pow_self).trans ((length_tab_codeOf_le _).trans (nu_le m))
  have h2 := h.1
  unfold nb bq bt
  omega
end CircuitLowerBound.Round
