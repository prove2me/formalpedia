-- Prove2me | solution 1 for CircuitLowerBound.Norm.wires_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:49:55.896474+00:00
-- url     : https://prove2.me/submissions/e479632e-caa8-4718-8bae-9a65904b9764

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Norm
import Theorems.Thm_CircuitLowerBound_Norm_value_ng

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Norm
namespace CircuitLowerBound.Norm
theorem _root_.solution (C : Circuit) (w : List Bool) : wires w (toC (norm w.length C)) = wires w C := by
  induction C generalizing w with
  | nil => rfl
  | cons G C ih =>
    have h := ih (w ++ [G.op (w.getD G.in₁ false) (w.getD G.in₂ false)])
    rw [List.length_append, List.length_singleton] at h
    change wires (w ++ [(ng w.length G).toGate.op (w.getD (ng w.length G).toGate.in₁ false) (w.getD (ng w.length G).toGate.in₂ false)])
      (toC (norm (w.length + 1) C)) = wires (w ++ [G.op (w.getD G.in₁ false) (w.getD G.in₂ false)]) C
    rw [value_ng, h]
end CircuitLowerBound.Norm
