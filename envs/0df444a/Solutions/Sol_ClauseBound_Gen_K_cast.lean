-- Prove2me | solution 1 for ClauseBound.Gen.K_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:33:41.64956+00:00
-- url     : https://prove2.me/submissions/961e5a4a-c02f-4e62-b6f8-93b2b6d31933

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Theorems.Thm_ClauseBound_Gen_K_eq

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen
open Levels.Gen
namespace ClauseBound.Gen
theorem _root_.solution (x₀ l : ℕ) : (K x₀ l : ℝ) = 2 ^ x x₀ l := by
  rw [K_eq]; push_cast; rfl
end ClauseBound.Gen
