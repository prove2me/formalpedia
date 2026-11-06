-- Prove2me | solution 1 for ExplicitCost.four_mul_le_xiAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:47:33.412773+00:00
-- url     : https://prove2.me/submissions/ec3e9f02-5250-49bc-bbfa-80ffda1737a0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelBound
import Theorems.Thm_ExplicitCost_two_pow_le_g


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (hx : 1 ≤ x₀) (ρ : ℝ) (c l lam B j : ℕ) (hB : 1 ≤ bitsAt ρ c x₀ l lam B (j + 1)) : 4 * lamAt ρ c x₀ l lam B (j + 1) + 4 ≤ xiAt ρ c x₀ l lam B j := by
  have hp : 2 ^ 1 ≤ 2 ^ x₀ := Nat.pow_le_pow_right (by norm_num) hx
  have hg : 2 ≤ g x₀ j := le_trans hp (two_pow_le_g x₀ j)
  have h4 : 2 ^ 2 ≤ g x₀ j ^ 2 := Nat.pow_le_pow_left hg 2
  have := Nat.mul_le_mul h4 (le_refl (lamAt ρ c x₀ l lam B (j + 1) + bitsAt ρ c x₀ l lam B (j + 1)))
  unfold xiAt Xi
  omega
end ExplicitCost
