-- Prove2me | solution 1 for ExplicitCost.room_le_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:19:43.386078+00:00
-- url     : https://prove2.me/submissions/6b279e2f-6a28-4d52-b5ac-736aad8de2c2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RoomWithin

set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed Finset
namespace ExplicitCost
theorem _root_.solution {u P X c : ℕ} (hP : P ≤ X ^ c) (hX : 8 ≤ X) (hc : 1 ≤ c) (hu : 1 ≤ u) : (u + P + 8) * (P + 8) ≤ u * X ^ (2 * c + 3) := by
  have h1 : X ≤ X ^ c := Nat.le_self_pow (by omega) _
  have h2 : P + 8 ≤ X ^ (c + 1) := by
    have : 2 * X ^ c ≤ X * X ^ c := Nat.mul_le_mul_right _ (by omega)
    have e : X ^ (c + 1) = X * X ^ c := by ring
    omega
  have h3 : 1 ≤ X ^ (c + 1) := Nat.pow_pos (by omega)
  have h4 : u + P + 8 ≤ u * X ^ (c + 2) := by
    have a1 : u ≤ u * X ^ (c + 1) := Nat.le_mul_of_pos_right _ h3
    have a2 : X ^ (c + 1) ≤ u * X ^ (c + 1) := Nat.le_mul_of_pos_left _ hu
    have a3 : 2 * (u * X ^ (c + 1)) ≤ X * (u * X ^ (c + 1)) := Nat.mul_le_mul_right _ (by omega)
    have e : u * X ^ (c + 2) = X * (u * X ^ (c + 1)) := by ring
    omega
  calc (u + P + 8) * (P + 8) ≤ (u * X ^ (c + 2)) * X ^ (c + 1) := Nat.mul_le_mul h4 h2
    _ = u * X ^ (2 * c + 3) := by ring
end ExplicitCost
