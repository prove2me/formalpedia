-- Prove2me | solution 1 for CircuitLowerBound.Tab.ops_le_dep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:33:56.215809+00:00
-- url     : https://prove2.me/submissions/68ec8478-c54d-47e8-83a1-680ebd1fdc55

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
theorem _root_.solution (l : N.tm.Λ) : ops (N.tm.m l) ≤ dep N :=
  le_trans (Finset.le_sup (f := fun l : N.tm.Λ => ops (N.tm.m l)) (Finset.mem_univ l)) (le_max_right _ _)
end CircuitLowerBound.Tab
