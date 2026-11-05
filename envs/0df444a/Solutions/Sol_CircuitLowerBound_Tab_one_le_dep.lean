-- Prove2me | solution 1 for CircuitLowerBound.Tab.one_le_dep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:42:41.614088+00:00
-- url     : https://prove2.me/submissions/e28769d2-9e5a-440a-9d35-6f98f2f02035

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
namespace CircuitLowerBound.Tab
theorem _root_.solution : 1 ≤ dep N := le_max_left _ _
end CircuitLowerBound.Tab
