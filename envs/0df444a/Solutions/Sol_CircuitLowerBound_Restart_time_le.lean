-- Prove2me | solution 1 for CircuitLowerBound.Restart.time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:52:17.574172+00:00
-- url     : https://prove2.me/submissions/f127032f-77d9-4c0e-81e1-26fcfc8afe65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_ENP_Round
import Definitions.Def_CircuitLowerBound_Small
import Definitions.Def_CountKSatRate_Pad
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Restart

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork PaddedDescent Turing
open CircuitLowerBound.Restart
namespace CircuitLowerBound.Restart
theorem _root_.solution (q m a : ℕ) (ha : a ≤ 2 ^ m) : q * (2 * m + 1 + a + 2 ^ (2 * m + 4) + 1) ^ q ≤ 2 ^ ((6 * q + 1) * (m + 1)) := by
  have h1 : 2 * m + 1 + a + 2 ^ (2 * m + 4) + 1 ≤ 2 ^ (2 * m + 5) := by
    have a1 : m < 2 ^ m := Nat.lt_two_pow_self
    have a2 : 2 ^ (m + 2) ≤ 2 ^ (2 * m + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a3 : 2 ^ (m + 2) = 2 ^ m * 4 := by rw [pow_add]; norm_num
    have a4 : 2 ^ (2 * m + 5) = 2 ^ (2 * m + 4) * 2 := pow_succ 2 _
    omega
  have h2 : q + (2 * m + 5) * q + (4 * q * m + m + 1) = (6 * q + 1) * (m + 1) := by ring
  calc q * (2 * m + 1 + a + 2 ^ (2 * m + 4) + 1) ^ q ≤ 2 ^ q * (2 ^ (2 * m + 5)) ^ q :=
        Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.pow_le_pow_left h1 q)
    _ = 2 ^ (q + (2 * m + 5) * q) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((6 * q + 1) * (m + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
end CircuitLowerBound.Restart
