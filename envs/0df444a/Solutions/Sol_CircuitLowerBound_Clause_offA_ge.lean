-- Prove2me | solution 1 for CircuitLowerBound.Clause.offA_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:44:01.964211+00:00
-- url     : https://prove2.me/submissions/41bc6092-44f2-4ffb-b65f-c90b5199e9a2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
namespace CircuitLowerBound.Clause
theorem _root_.solution (n bq bt rb R nf ι : ℕ) : n + 2 + rb * R + R * (3 * nf) ≤ offA n bq bt rb R nf ι := Nat.le_add_right _ _
end CircuitLowerBound.Clause
