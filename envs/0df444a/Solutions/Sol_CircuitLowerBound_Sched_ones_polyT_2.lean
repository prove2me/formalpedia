-- Prove2me | solution 2 for CircuitLowerBound.Sched.ones_polyT
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:17:27.82778+00:00
-- url     : https://prove2.me/submissions/e4ca81fd-452e-45c8-a9e4-a193f5436924

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_takeWhile
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Sched
open ENP Groundwork
variable {α : Type} [Enc α]

theorem solution {w : α → List Bool} (hw : PolyT w) : PolyT fun x => ones (w x) := by
  exact Groundwork.PolyT.length
    (Groundwork.PolyT.takeWhile
      (Groundwork.PolyT.snd P2M_Groundwork_PolyT_id__1c5d0f44cc8f) hw)
