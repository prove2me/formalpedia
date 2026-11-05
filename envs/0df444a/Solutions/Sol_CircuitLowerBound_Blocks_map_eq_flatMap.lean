-- Prove2me | solution 1 for CircuitLowerBound.Blocks.map_eq_flatMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:38:23.805595+00:00
-- url     : https://prove2.me/submissions/dc135560-3523-4d50-ba5e-1fff002e3fbb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Blocks

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Blocks
open ENP Groundwork
namespace CircuitLowerBound.Blocks
theorem _root_.solution {α : Type} (g : ℕ → α) (w : ℕ) : (List.range w).map g = (List.range w).flatMap fun i => [g i] := by
  induction w with
  | zero => rfl
  | succ w ih => rw [List.range_succ, List.map_append, List.flatMap_append, ih]; rfl
end CircuitLowerBound.Blocks
