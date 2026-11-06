-- Prove2me | solution 1 for ExplicitCost.one_le_bitsAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:20:52.988105+00:00
-- url     : https://prove2.me/submissions/c4da517c-255c-42dd-b82f-b688b56ac1c2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChainLabel
import Theorems.Thm_ExplicitCost_bitsAt_self
import Theorems.Thm_ExplicitCost_bitsAt_of_lt
import Theorems.Thm_ExplicitCost_one_le_lamAt
import Theorems.Thm_ExplicitCost_g_pos
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (hN : Numbers ρ c x₀ lam B) (hj : j ≤ l) : 1 ≤ bitsAt ρ c x₀ l lam B j := by
  rcases Nat.lt_or_ge j l with h | h
  · rw [bitsAt_of_lt ρ c x₀ lam B h]
    have h1 := one_le_lamAt hN (by omega : j + 1 ≤ l)
    have h2 : 1 ≤ g x₀ j ^ 2 := Nat.pow_pos (g_pos x₀ j)
    have h3 : 1 ≤ (2 * lamAt ρ c x₀ l lam B (j + 1)) ^ c := Nat.pow_pos (by omega)
    have h4 : 1 ≤ g x₀ j ^ 2 * (2 * lamAt ρ c x₀ l lam B (j + 1)) ^ c := Nat.mul_pos h2 h3
    have h5 : 1 ≤ g x₀ j ^ 2 * bitsOne c (g x₀ j) (lamAt ρ c x₀ l lam B (j + 1)) (bitsAt ρ c x₀ l lam B (j + 1)) := Nat.mul_pos h2 (by unfold bitsOne; omega)
    exact h5.trans (Nat.le_add_left _ _)
  · obtain rfl : j = l := by omega
    rw [bitsAt_self]
    exact hN.B_pos
end ExplicitCost
