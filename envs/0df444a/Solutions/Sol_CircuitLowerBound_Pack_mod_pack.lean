-- Prove2me | solution 1 for CircuitLowerBound.Pack.mod_pack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:40:29.701397+00:00
-- url     : https://prove2.me/submissions/6140f675-d975-48d2-8ffd-6365eb467466

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Pack

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP
open CircuitLowerBound.Pack
namespace CircuitLowerBound.Pack
theorem _root_.solution {x y M : ℕ} (h : y < M) : (x * M + y) % M = y := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]
end CircuitLowerBound.Pack
