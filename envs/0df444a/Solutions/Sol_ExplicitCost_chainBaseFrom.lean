-- Prove2me | solution 1 for ExplicitCost.chainBaseFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:58:13.117999+00:00
-- url     : https://prove2.me/submissions/f098e936-9fbd-43e5-b0a6-57b16700a38e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ChainLabel
import Definitions.Def_CountedRecursion_CrudeBounds
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_CountedRecursion_PartAPrinted
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Chain
import Theorems.Thm_ExplicitCost_bitsAt_of_lt
import Theorems.Thm_ExplicitCost_one_le_bitsAt
import Theorems.Thm_ExplicitCost_one_le_lamAt


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
namespace ExplicitCost
theorem _root_.solution : ChainBaseFrom := by
  intro hL hC ρ c x₀ l lam B j hN hj
  obtain ⟨-, -, h3, -⟩ := hL ρ c x₀ l lam B j hN hj
  have h := (hC c x₀ j (lamAt ρ c x₀ l lam B (j + 1)) (bitsAt ρ c x₀ l lam B (j + 1)) (lamAt ρ c x₀ l lam B j) hN.x₀_ge (one_le_lamAt hN (by omega)) (one_le_bitsAt hN (by omega)) h3).2.2
  rw [← bitsAt_of_lt ρ c x₀ lam B hj] at h
  exact h
end ExplicitCost
