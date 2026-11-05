-- Prove2me | solution 1 for ClauseBound.TopN.Arith.pow_le_n
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:31:19.097604+00:00
-- url     : https://prove2.me/submissions/cf9e39c4-95da-404d-a810-404679ee3d56

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
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith
variable {k K n s : ℕ}
namespace ClauseBound.TopN.Arith
theorem _root_.solution (hK : 1 ≤ K) (hn : K ^ 17 ≤ n) {j : ℕ} (hj : j ≤ 17) : K ^ j ≤ n := (Nat.pow_le_pow_right hK hj).trans hn
end ClauseBound.TopN.Arith
