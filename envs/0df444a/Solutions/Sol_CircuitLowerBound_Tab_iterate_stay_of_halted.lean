-- Prove2me | solution 1 for CircuitLowerBound.Tab.iterate_stay_of_halted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:35:37.161791+00:00
-- url     : https://prove2.me/submissions/080087f6-4266-4ded-8c8a-288be773df74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Theorems.Thm_CircuitLowerBound_Tab_stay_of_halted

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
namespace CircuitLowerBound.Tab
theorem _root_.solution {c : N.tm.Cfg} (h : c.l = none) (n : ℕ) : (stay N)^[n] c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, stay_of_halted N h, ih]
end CircuitLowerBound.Tab
