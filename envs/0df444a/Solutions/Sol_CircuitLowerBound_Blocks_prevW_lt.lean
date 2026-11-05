-- Prove2me | solution 1 for CircuitLowerBound.Blocks.prevW_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:31:20.333858+00:00
-- url     : https://prove2.me/submissions/218f3f69-0e4b-4921-8c23-a559e16defa8

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
theorem _root_.solution {off init i : ℕ} (h : init < off) : prevW off init i < off + i := by
  unfold prevW; split_ifs <;> omega
end CircuitLowerBound.Blocks
