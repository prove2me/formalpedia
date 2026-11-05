-- Prove2me | solution 1 for ClauseBound.Boson.Final.factorial_lt_two_pow_big
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:33:13.27252+00:00
-- url     : https://prove2.me/submissions/918a697f-7e09-4e17-a1ec-b23a8b5b7864

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_ClauseBound_Boson_Final

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Final
namespace ClauseBound.Boson.Final
theorem _root_.solution (h : ℕ) : h.factorial < 2 ^ big h := by
  have h1 : h * h < big h := by
    have : h * h < 40 * (h + 1) ^ 2 := by nlinarith
    exact this.trans_le (Nat.le_add_right _ _)
  calc h.factorial ≤ h ^ h := Nat.factorial_le_pow h
    _ ≤ (2 ^ h) ^ h := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := h)).le h
    _ = 2 ^ (h * h) := (pow_mul 2 h h).symm
    _ < 2 ^ big h := Nat.pow_lt_pow_right (by norm_num) h1
end ClauseBound.Boson.Final
