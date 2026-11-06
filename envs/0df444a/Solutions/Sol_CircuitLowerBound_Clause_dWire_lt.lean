-- Prove2me | solution 1 for CircuitLowerBound.Clause.dWire_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:44:03.318085+00:00
-- url     : https://prove2.me/submissions/e358c938-eb1b-4fb8-a519-65efb22801f9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Clause_Fw_lt

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
namespace CircuitLowerBound.Clause
theorem _root_.solution (n rb R kbm Dq : ℕ) {ι : ℕ} (hι : ι < 3) (i : ℕ) : dWire n rb R kbm Dq ι i < n + 2 + rb * R + R * (3 * (5 + kbm + Dq)) := by
  unfold dWire
  split_ifs with h
  · exact Fw_lt n rb R hι (by omega)
  · omega
end CircuitLowerBound.Clause
