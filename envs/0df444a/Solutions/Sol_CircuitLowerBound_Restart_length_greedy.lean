-- Prove2me | solution 1 for CircuitLowerBound.Restart.length_greedy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:46:57.053227+00:00
-- url     : https://prove2.me/submissions/f201afce-7a49-451d-ac1f-14d786c428f1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_ENP_Round
import Definitions.Def_CircuitLowerBound_Small
import Definitions.Def_CountKSatRate_Pad
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Restart
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork PaddedDescent Turing
open CircuitLowerBound.Restart
namespace CircuitLowerBound.Restart
theorem _root_.solution (φ : Cnf) (j : ℕ) : (greedy φ j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [greedy, List.length_append, ih]; rfl
end CircuitLowerBound.Restart
