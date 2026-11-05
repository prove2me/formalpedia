-- Prove2me | solution 1 for ClauseBound.TopN.Arith.size_n_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:38:42.755797+00:00
-- url     : https://prove2.me/submissions/6d480021-beff-4c15-b775-4391ef2430ce

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
import Theorems.Thm_ClauseBound_TopN_Arith_succ_le_two_pow
import Theorems.Thm_Groundwork_RebalanceArith_size_le


set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith
variable {k K n s C₀ : ℕ}
namespace ClauseBound.TopN.Arith
theorem _root_.solution (hlt : n < K ^ (17 * C₀)) : n.size ≤ 17 * C₀ * K.size := Nat.size_le.2 (succ_le_two_pow hlt)
end ClauseBound.TopN.Arith
