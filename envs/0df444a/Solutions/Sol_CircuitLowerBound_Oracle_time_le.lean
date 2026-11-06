-- Prove2me | solution 1 for CircuitLowerBound.Oracle.time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:49:01.623593+00:00
-- url     : https://prove2.me/submissions/f71cb697-950a-47e6-a403-c623e40e7612

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Runs
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Restart
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Turing Groundwork.TM
open CircuitLowerBound.Oracle
variable {M : TM2ComputableAux Bool Bool}
namespace CircuitLowerBound.Oracle
theorem _root_.solution (c n : ℕ) :
    (2 ^ (c * (n + 1)) + 1) * (3 * (0 + 2 ^ (c * (n + 1))) + 3 * n + 2 ^ (c * (n + 1)) + 12) ≤ 2 ^ ((2 * c + 7) * (n + 1)) := by
  have hY : 1 ≤ 2 ^ (c * (n + 1)) := Nat.one_le_two_pow
  have hn : n + 1 ≤ 2 ^ (n + 1) := Nat.lt_two_pow_self.le
  have h6 : 2 ^ 6 ≤ 2 ^ (6 * (n + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : 2 ^ ((2 * c + 7) * (n + 1)) = 2 ^ (c * (n + 1)) * 2 ^ (c * (n + 1)) * (2 ^ (6 * (n + 1)) * 2 ^ (n + 1)) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [e]
  generalize 2 ^ (c * (n + 1)) = Y at hY ⊢
  generalize 2 ^ (n + 1) = Z at hn ⊢
  generalize 2 ^ (6 * (n + 1)) = U at h6 ⊢
  have h1 : Y + 1 ≤ 2 * Y := by omega
  have hZ : 1 ≤ Z := by omega
  have h2 : 3 * (0 + Y) + 3 * n + Y + 12 ≤ 19 * (Y * Z) := by nlinarith
  calc (Y + 1) * (3 * (0 + Y) + 3 * n + Y + 12) ≤ 2 * Y * (19 * (Y * Z)) := Nat.mul_le_mul h1 h2
    _ = Y * Y * (38 * Z) := by ring
    _ ≤ Y * Y * (U * Z) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by norm_num at h6; omega))
end CircuitLowerBound.Oracle
