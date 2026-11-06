-- Prove2me | solution 2 for CircuitLowerBound.Inf.Avail.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:01:54.889472+00:00
-- url     : https://prove2.me/submissions/8b6588e6-3136-4065-bb70-eba93db3eca7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
import Theorems.Thm_CircuitLowerBound_Inf_wires_append
import Theorems.Thm_CircuitLowerBound_Inf_length_wires
import Theorems.Thm_CircuitLowerBound_Inf_prefix_wires
import Theorems.Thm_CircuitLowerBound_Inf_getD_of_prefix
import Theorems.Thm_CircuitLowerBound_Blocks_getD_of_prefix
import Theorems.Thm_CircuitLowerBound_Blocks_prefix_wires
import Theorems.Thm_CircuitLowerBound_Form_length_wires


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Inf
open ENP
namespace CircuitLowerBound.Inf
namespace Avail
theorem _root_.solution {n : ℕ} {C : Circuit} {g : List Bool → Bool} (h : Avail n C g) (D : Circuit) : Avail n (C ++ D) g := by
  obtain ⟨w, hw, h⟩ := h
  refine ⟨w, by rw [List.length_append]; omega, fun x hx => ?_⟩
  rw [wires_append, getD_of_prefix (prefix_wires _ D) (by rw [length_wires, hx]; exact hw), h x hx]
end Avail
end CircuitLowerBound.Inf
