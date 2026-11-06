-- Prove2me | solution 1 for CircuitLowerBound.Norm.toGate_op
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:39:47.231674+00:00
-- url     : https://prove2.me/submissions/31f97c0a-3e91-4379-9abf-33de5dfdabca

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Norm

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Norm
namespace CircuitLowerBound.Norm
theorem _root_.solution (n : ℕ) (G : Gate) (x y : Bool) : (ng n G).toGate.op x y = op' n G x y := by
  cases x <;> cases y <;> rfl
end CircuitLowerBound.Norm
