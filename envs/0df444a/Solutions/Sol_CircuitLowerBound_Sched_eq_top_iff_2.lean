-- Prove2me | solution 2 for CircuitLowerBound.Sched.eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:17:40.550281+00:00
-- url     : https://prove2.me/submissions/62e80dad-6dec-4d87-91b1-32673ec8b438

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
import Theorems.Thm_CircuitLowerBound_Sched_lt_top_iff

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Sched
open ENP Groundwork
variable {α : Type} [Enc α]
namespace CircuitLowerBound.Sched
theorem _root_.solution (a s : ℕ) : s = top a ↔ (leTop a s && !leTop a (s - 1)) = true := by
  rw [Bool.and_eq_true, ← top_le_iff, ← lt_top_iff]
  have : 0 < top a := by unfold top; positivity
  omega
end CircuitLowerBound.Sched
