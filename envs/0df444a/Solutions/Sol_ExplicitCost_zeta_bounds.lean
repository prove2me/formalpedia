-- Prove2me | solution 1 for ExplicitCost.zeta_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:13:28.009682+00:00
-- url     : https://prove2.me/submissions/9e2dd952-e0cb-4128-bf69-8ac49a9e3e27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChainLabel

set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (j : ℕ) : 0 < zeta j ∧ zeta j ≤ 1 / 32 := by
  have h : (2 : ℝ) ^ 5 ≤ 2 ^ (j + 5) := pow_le_pow_right₀ (by norm_num) (by omega)
  unfold zeta
  refine ⟨by positivity, one_div_le_one_div_of_le (by norm_num) ?_⟩
  norm_num at h
  exact h
end ExplicitCost
