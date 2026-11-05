-- Prove2me | solution 1 for ClauseBound.Gen.logb_K
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:14:40.79263+00:00
-- url     : https://prove2.me/submissions/6feff0cc-e300-4e7b-9237-f4d74ae76bef

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Theorems.Thm_ClauseBound_Gen_K_cast

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen
open Levels.Gen
namespace ClauseBound.Gen
theorem _root_.solution (x₀ l : ℕ) : Real.logb 2 (K x₀ l) = x x₀ l := by
  rw [K_cast, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
end ClauseBound.Gen
