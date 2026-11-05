-- Prove2me | solution 1 for ClauseBound.TopN.Arith.b_le_lin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:29.541643+00:00
-- url     : https://prove2.me/submissions/82d9f177-9aab-4084-9cc0-6f53789237c2

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
variable {k K n s : ℕ}
namespace ClauseBound.TopN.Arith
theorem _root_.solution (k s : ℕ) : betaN k s + 3 ≤ (17 * (2 ^ (k + 1) + 1) + k + 6) * (s + 1) := by
  unfold betaN
  generalize 2 ^ (k + 1) + 1 = c
  nlinarith [Nat.zero_le (c * s), Nat.zero_le (k * s), Nat.zero_le s]
end ClauseBound.TopN.Arith
