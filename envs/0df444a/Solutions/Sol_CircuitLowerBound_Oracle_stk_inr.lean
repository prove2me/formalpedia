-- Prove2me | solution 1 for CircuitLowerBound.Oracle.stk_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:58:36.275192+00:00
-- url     : https://prove2.me/submissions/81ae4fdd-82e8-4aa3-9eba-d98a399d1c6b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_TM_Run
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Machine

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable (M : TM2ComputableAux Bool Bool)
variable {M}
namespace CircuitLowerBound.Oracle
theorem _root_.solution (T : ∀ k, List (M.tm.Γ k)) (n : NS → List Bool) (j : NS) : stk M T n (.inr j) = n j := rfl
end CircuitLowerBound.Oracle
