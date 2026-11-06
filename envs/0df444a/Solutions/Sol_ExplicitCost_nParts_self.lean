-- Prove2me | solution 1 for ExplicitCost.nParts_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:06:20.078964+00:00
-- url     : https://prove2.me/submissions/7cdd8c43-bdc1-49ab-aa7d-5bf336084731

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_SquareGrid

set_option autoImplicit false
section
section
open ExplicitCost
open ClauseBound.Alg
namespace ExplicitCost
theorem _root_.solution (g : ℕ) (tr : Bool) : nParts g g tr = g := by cases tr <;> rfl
end ExplicitCost
