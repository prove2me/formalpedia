-- Prove2me | solution 1 for CircuitLowerBound.Blocks.getD_of_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:27:35.39444+00:00
-- url     : https://prove2.me/submissions/71f71312-aba3-463c-b547-3fcbade1bb03

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
theorem _root_.solution {l₁ l₂ : List Bool} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) : l₂.getD i false = l₁.getD i false := by
  obtain ⟨r, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi
end CircuitLowerBound.Blocks
