-- Prove2me | solution 1 for ExplicitCost.towerSize_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:19:32.012461+00:00
-- url     : https://prove2.me/submissions/f33c4e93-1160-4e37-9c2e-810c2de5dfd8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_TotalRoom
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed QueryMachines Finset
namespace ExplicitCost
theorem _root_.solution {l R m Y : ℕ} (hm : m = l + 3) (hY : 1 ≤ Y) (hR : R ≤ m * Y) : Tower.towerSize l R R R ≤ 5 * (m ^ 3 * Y) := by
  have a0 : 1 ≤ m * Y := Nat.mul_pos (by omega) hY
  have a1 : l * (R + 1) + R + R + 3 ≤ m * (R + 1) := by
    have : m * (R + 1) = l * (R + 1) + 3 * (R + 1) := by rw [hm]; ring
    omega
  have a2 : R + 1 ≤ 2 * (m * Y) := by omega
  have a3 : (2 * l + 2) * (l * (R + 1) + R + R + 3) ≤ (2 * m) * (m * (2 * (m * Y))) := Nat.mul_le_mul (by omega) (a1.trans (Nat.mul_le_mul_left _ a2))
  have a4 : (2 * m) * (m * (2 * (m * Y))) = 4 * (m ^ 3 * Y) := by ring
  have a5 : 1 ≤ m ^ 3 * Y := Nat.mul_pos (Nat.pow_pos (by omega)) hY
  unfold Tower.towerSize
  omega
end ExplicitCost
