-- Prove2me | solution 1 for ExplicitCost.two_pow_le_K
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:03.547358+00:00
-- url     : https://prove2.me/submissions/47e93a38-95be-4a2b-ad83-e9326ceeb671

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_Numbers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelNumbers
import Theorems.Thm_ExplicitCost_K_mono


set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen
namespace ExplicitCost
theorem _root_.solution (x₀ j : ℕ) : 2 ^ x₀ ≤ K x₀ j := K_mono x₀ (Nat.zero_le j)
end ExplicitCost
