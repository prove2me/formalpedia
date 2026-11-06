-- Prove2me | solution 2 for CircuitLowerBound.Pack.bt_le_bq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:15:13.751701+00:00
-- url     : https://prove2.me/submissions/23093280-0cfd-4d68-9a05-e648218aa192

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
variable {e : MCode} {L P : ℕ}
namespace CircuitLowerBound.Pack
theorem _root_.solution (e : MCode) (L : ℕ) : 2 ^ bt e L ≤ 2 ^ bq e L := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
end CircuitLowerBound.Pack
