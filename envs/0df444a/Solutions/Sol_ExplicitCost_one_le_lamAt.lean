-- Prove2me | solution 1 for ExplicitCost.one_le_lamAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:11:51.647201+00:00
-- url     : https://prove2.me/submissions/7fb00ba4-bd5f-4312-a16a-273fa3d6172c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChainLabel
import Theorems.Thm_ExplicitCost_lamAt_pos

set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
namespace ExplicitCost
theorem _root_.solution (hN : Numbers ρ c x₀ lam B) (hj : j ≤ l) : 1 ≤ lamAt ρ c x₀ l lam B j := lamAt_pos hN l (l - j) j (by omega)
end ExplicitCost
