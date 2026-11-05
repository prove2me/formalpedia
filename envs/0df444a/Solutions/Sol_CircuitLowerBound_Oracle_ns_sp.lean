-- Prove2me | solution 1 for CircuitLowerBound.Oracle.ns_sp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:02:17.005008+00:00
-- url     : https://prove2.me/submissions/96b82379-6465-4669-94f2-5f5a2ed3986d

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
variable (a b c w : List Bool)
namespace CircuitLowerBound.Oracle
theorem _root_.solution : ns a b c .sp = c := rfl
end CircuitLowerBound.Oracle
