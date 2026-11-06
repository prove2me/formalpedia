-- Prove2me | solution 1 for ExplicitCost.pos_of_chainLabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:23:59.188935+00:00
-- url     : https://prove2.me/submissions/39af9cff-4aef-43b2-bf11-43c076e4d8aa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelBound
import Theorems.Thm_ExplicitCost_bitsAt_self
import Theorems.Thm_ExplicitCost_lamAt_self


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (hL : ChainLabel) (hN : Numbers ρ c x₀ lam B) (hj : j ≤ l) : 1 ≤ lamAt ρ c x₀ l lam B j ∧ 1 ≤ bitsAt ρ c x₀ l lam B j := by
  rcases Nat.lt_or_ge j l with h | h
  · exact ⟨(hL ρ c x₀ l lam B j hN h).1, (hL ρ c x₀ l lam B j hN h).2.1⟩
  · obtain rfl : j = l := by omega
    rw [lamAt_self, bitsAt_self]
    exact ⟨hN.lam_pos, hN.B_pos⟩
end ExplicitCost
