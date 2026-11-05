-- Prove2me | solution 1 for ClauseBound.TopN.Arith.succ_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:35:40.423564+00:00
-- url     : https://prove2.me/submissions/5c326efc-52e6-4df0-8208-4e7836b5a5c0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_TopN_Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_ClauseBound_TopN_Arith

set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith
variable {k K n s C₀ : ℕ}
namespace ClauseBound.TopN.Arith
theorem _root_.solution (hlt : n < K ^ (17 * C₀)) : n + 1 ≤ 2 ^ (17 * C₀ * K.size) := by
  have h1 : K ≤ 2 ^ K.size := (Nat.lt_size_self K).le
  calc n + 1 ≤ K ^ (17 * C₀) := hlt
    _ ≤ (2 ^ K.size) ^ (17 * C₀) := Nat.pow_le_pow_left h1 _
    _ = 2 ^ (17 * C₀ * K.size) := by rw [← pow_mul, Nat.mul_comm]
end ClauseBound.TopN.Arith
