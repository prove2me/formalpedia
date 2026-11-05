-- Prove2me | solution 1 for ClauseBound.Gen.x_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:14:39.663196+00:00
-- url     : https://prove2.me/submissions/0a3575fb-d1a0-4c33-82b1-aede2ee894b3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen
open Levels.Gen
namespace ClauseBound.Gen
theorem _root_.solution (x₀ l : ℕ) (hx : 18 ≤ x₀) : x₀ + 2 * l ≤ x x₀ l := by
  induction l with
  | zero => simp [x]
  | succ l ih => rw [x]; omega
end ClauseBound.Gen
