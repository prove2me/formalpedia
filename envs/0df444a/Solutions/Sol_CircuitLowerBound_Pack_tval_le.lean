-- Prove2me | solution 1 for CircuitLowerBound.Pack.tval_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:15:11.574192+00:00
-- url     : https://prove2.me/submissions/e8778b03-2bf7-4d8a-8de0-d9a661667793

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
theorem _root_.solution {b t : ℕ} (ht : t < 2 ^ b) (mode : ℕ) : tval b t mode ≤ 2 ^ b := by
  unfold tval
  split_ifs <;> omega
end CircuitLowerBound.Pack
