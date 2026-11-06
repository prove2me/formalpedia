-- Prove2me | solution 2 for CircuitLowerBound.Inf.ext_proj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:50:54.333909+00:00
-- url     : https://prove2.me/submissions/5cba6243-1148-4e6b-9a1a-64da8e374353

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
import Theorems.Thm_CircuitLowerBound_Inf_prefix_wires
import Theorems.Thm_CircuitLowerBound_Inf_getD_of_prefix
import Theorems.Thm_CircuitLowerBound_Blocks_getD_of_prefix
import Theorems.Thm_CircuitLowerBound_Blocks_prefix_wires


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Inf
open ENP
namespace CircuitLowerBound.Inf
theorem _root_.solution {n i : ℕ} (hi : i < n) : Ext n fun x => x.getD i false := fun C₀ =>
  ⟨[], i, by omega, fun x hx => by rw [List.append_nil]; exact getD_of_prefix (prefix_wires x C₀) (by omega)⟩
end CircuitLowerBound.Inf
