-- Prove2me | solution 1 for CircuitLowerBound.TabF.length_rest_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:35:18.395192+00:00
-- url     : https://prove2.me/submissions/6b91e974-11bd-4085-96f8-250cfde917ab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]
namespace CircuitLowerBound.TabF
theorem _root_.solution (x : List Bool) : (rest x).length ≤ x.length := by
  unfold rest
  rw [List.length_tail]
  have := (List.dropWhile_sublist (l := x) id).length_le
  omega
end CircuitLowerBound.TabF
