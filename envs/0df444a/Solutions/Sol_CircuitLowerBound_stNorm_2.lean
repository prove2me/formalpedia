-- Prove2me | solution 2 for CircuitLowerBound.stNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:54:08.835662+00:00
-- url     : https://prove2.me/submissions/d828fa30-c591-4405-b8ff-7b7dab82c4b2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Norm
import Theorems.Thm_CircuitLowerBound_Norm_length_norm
import Theorems.Thm_CircuitLowerBound_Norm_wires_norm
import Theorems.Thm_CircuitLowerBound_Norm_wf_norm

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Norm
namespace CircuitLowerBound
theorem _root_.solution : StNorm := by
  intro m C hm
  refine ⟨norm m C, wf_norm C m hm, length_norm C m, fun x hx => ?_⟩
  unfold eval
  rw [← hx, wires_norm]
end CircuitLowerBound
