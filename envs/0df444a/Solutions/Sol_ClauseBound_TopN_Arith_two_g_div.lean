-- Prove2me | solution 1 for ClauseBound.TopN.Arith.two_g_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:49:44.545207+00:00
-- url     : https://prove2.me/submissions/aba20d68-3fed-4928-bd2c-17b8c7e24fcb

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
theorem _root_.solution (hK : 1 ≤ K) : 2 * (3 * K ^ 8) / K = 6 * K ^ 7 := by
  rw [show 2 * (3 * K ^ 8) = 6 * K ^ 7 * K by ring]
  exact Nat.mul_div_cancel _ hK
end ClauseBound.TopN.Arith
