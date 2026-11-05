-- Prove2me | solution 1 for ClauseBound.Gen.K_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:32:38.387637+00:00
-- url     : https://prove2.me/submissions/ecaa2df2-4bce-49ee-8fef-696fc3158d5a

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
theorem _root_.solution (x₀ l : ℕ) : K x₀ l = 2 ^ x x₀ l := by
  induction l with
  | zero => rfl
  | succ l ih => rw [K, x, ih, ← pow_add, ← pow_mul, Nat.mul_comm]
end ClauseBound.Gen
