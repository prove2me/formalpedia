-- Prove2me | solution 1 for CircuitLowerBound.Tab.stay_of_halted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:34:00.716493+00:00
-- url     : https://prove2.me/submissions/3b4e160b-9ae8-46da-9604-5d27ea969bcf

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
theorem _root_.solution {c : N.tm.Cfg} (h : c.l = none) : stay N c = c := by
  obtain ⟨l, v, S⟩ := c
  subst h
  rfl
end CircuitLowerBound.Tab
