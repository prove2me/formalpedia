-- Prove2me | solution 1 for ExplicitCost.base_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:16:42.536889+00:00
-- url     : https://prove2.me/submissions/f48cc036-5f8a-4601-ae6d-296cea497ff7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Definitions.Def_GeneralPieces_Rec_Rate
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CountBase
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
namespace ExplicitCost
theorem _root_.solution {A k X n t : ℕ} (hk : 1 ≤ k) (hX : 2 * k ≤ X) (hn : 2 ≤ n) (ht : 1 ≤ t) : A * (k + 1) + 0 * 0 + A * k * t ≤ t * (A * X ^ n) := by
  have h1 : (2 * k) ^ 2 ≤ X ^ n := (Nat.pow_le_pow_left hX 2).trans (Nat.pow_le_pow_right (by omega) hn)
  have h2 : 3 * k ≤ (2 * k) ^ 2 := by
    have a := Nat.le_mul_self k
    have e : (2 * k) ^ 2 = 4 * (k * k) := by ring
    omega
  have h3 : k + 1 + k * t ≤ t * (3 * k) := by
    have a : k ≤ k * t := Nat.le_mul_of_pos_right _ ht
    have e : t * (3 * k) = 3 * (k * t) := by ring
    omega
  calc A * (k + 1) + 0 * 0 + A * k * t = A * (k + 1 + k * t) := by ring
    _ ≤ A * (t * X ^ n) := Nat.mul_le_mul_left _ (h3.trans (Nat.mul_le_mul_left _ (h2.trans h1)))
    _ = t * (A * X ^ n) := by ring
end ExplicitCost
