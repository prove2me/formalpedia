-- Prove2me | solution 1 for CircuitLowerBound.Blocks.num_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:28:11.195034+00:00
-- url     : https://prove2.me/submissions/608d507b-87bd-48bb-99a2-87c5aa9d0a59

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
theorem _root_.solution {b c : ℕ → Bool} {w : ℕ} (h : ∀ i < w, b i = c i) : num b w = num c w := by
  unfold num
  exact congrArg ofWord (List.map_congr_left fun i hi => h i (List.mem_range.1 hi))
end CircuitLowerBound.Blocks
