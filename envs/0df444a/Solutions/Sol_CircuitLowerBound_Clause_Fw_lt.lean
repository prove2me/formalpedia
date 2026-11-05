-- Prove2me | solution 1 for CircuitLowerBound.Clause.Fw_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:48:59.877199+00:00
-- url     : https://prove2.me/submissions/a62208f3-80ef-41f2-b651-f2f4042ed941

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Blocks_prevW_lt


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
namespace CircuitLowerBound.Clause
theorem _root_.solution (n rb R : ℕ) {nf ι f : ℕ} (hι : ι < 3) (hf : f < nf) : Fw n rb R nf ι f < n + 2 + rb * R + R * (3 * nf) := by
  have h1 : Fw n rb R nf ι f < n + 2 + rb * R + R * (ι * nf + f) + R := prevW_lt (by omega)
  have h2 : R * (ι * nf + f + 1) ≤ R * (3 * nf) := Nat.mul_le_mul_left _ (by nlinarith)
  rw [Nat.mul_succ] at h2
  omega
end CircuitLowerBound.Clause
