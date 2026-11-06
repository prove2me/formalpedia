-- Prove2me | solution 1 for ExplicitCost.chainLabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:31:25.354918+00:00
-- url     : https://prove2.me/submissions/03e5b8df-b533-41b6-89b9-25437f914d2a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChainLabel
import Theorems.Thm_ExplicitCost_lamAt_of_lt
import Theorems.Thm_ExplicitCost_quotient_at
import Theorems.Thm_ExplicitCost_one_le_lamAt
import Theorems.Thm_ExplicitCost_one_le_bitsAt
import Theorems.Thm_ClauseBound_Gen_Pick_K_pos
import Theorems.Thm_ExplicitCost_K_pos


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution : ChainLabel := by
  intro ρ c x₀ l lam B j hN hj
  have hΛ := one_le_lamAt hN (by omega : j + 1 ≤ l)
  obtain ⟨q1, q2⟩ := quotient_at hN j hΛ
  have hK : (0 : ℝ) < (K x₀ j : ℝ) ^ 2 := by
    have : (0 : ℝ) < K x₀ j := by exact_mod_cast K_pos x₀ j
    positivity
  refine ⟨one_le_lamAt hN hj.le, one_le_bitsAt hN hj.le, ?_, ?_⟩
  · rw [lamAt_of_lt ρ c x₀ lam B hj]
    exact Nat.floor_le_of_le (by push_cast; exact q2)
  · have h := Nat.floor_le (le_trans zero_le_one q1)
    rw [← lamAt_of_lt ρ c x₀ lam B hj] at h
    have h2 := mul_le_mul_of_nonneg_left h hK.le
    rwa [mul_div_cancel₀ _ hK.ne'] at h2
end ExplicitCost
