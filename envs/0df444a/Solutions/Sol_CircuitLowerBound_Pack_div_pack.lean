-- Prove2me | solution 1 for CircuitLowerBound.Pack.div_pack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:40:11.908391+00:00
-- url     : https://prove2.me/submissions/6e683320-d8a4-422d-8011-e87478effb70

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
theorem _root_.solution {x y M : ℕ} (h : y < M) : (x * M + y) / M = x := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h, Nat.zero_add]
end CircuitLowerBound.Pack
