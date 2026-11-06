-- Prove2me | solution 1 for ExplicitCost.lamAt_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:43.725707+00:00
-- url     : https://prove2.me/submissions/388bdc2f-1162-4f47-95d0-51338f48da3a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChainLabel
import Theorems.Thm_ExplicitCost_lamAt_self
import Theorems.Thm_ExplicitCost_lamAt_of_lt
import Theorems.Thm_ExplicitCost_quotient_at

set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (hN : Numbers ρ c x₀ lam B) (l : ℕ) : ∀ k j, j + k = l → 1 ≤ lamAt ρ c x₀ l lam B j := by
  intro k
  induction k with
  | zero =>
    intro j hj
    obtain rfl : j = l := by omega
    rw [lamAt_self]
    exact hN.lam_pos
  | succ k ih =>
    intro j hj
    rw [lamAt_of_lt ρ c x₀ lam B (by omega : j < l)]
    exact Nat.le_floor (by exact_mod_cast (quotient_at hN j (ih (j + 1) (by omega))).1)
end ExplicitCost
