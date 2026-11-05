-- Prove2me | solution 1 for CircuitLowerBound.Sched.lt_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:31:53.558915+00:00
-- url     : https://prove2.me/submissions/db59ebe6-3f47-4514-9425-2835c7873bd4

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
import Theorems.Thm_CircuitLowerBound_Sched_top_le_iff

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Sched
open ENP Groundwork
variable {α : Type} [Enc α]
namespace CircuitLowerBound.Sched
theorem _root_.solution (a s : ℕ) : s < top a ↔ (!leTop a s) = true := by
  rw [Bool.not_eq_true', ← Bool.not_eq_true, ← top_le_iff]
  omega
end CircuitLowerBound.Sched
