-- Prove2me | solution 1 for CircuitLowerBound.Blocks.wires_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:59:30.648052+00:00
-- url     : https://prove2.me/submissions/51ff30d2-ec5e-4f7d-bd3c-272bcfd7f3af

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Theorems.Thm_CircuitLowerBound_Blocks_prefix_wires
import Theorems.Thm_CircuitLowerBound_Blocks_getD_of_prefix

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Blocks
open ENP Groundwork
namespace CircuitLowerBound.Blocks
theorem _root_.solution (x : List Bool) (C : Circuit) {i : ℕ} (hi : i < x.length) : (wires x C).getD i false = x.getD i false :=
  getD_of_prefix (prefix_wires x C) hi
end CircuitLowerBound.Blocks
