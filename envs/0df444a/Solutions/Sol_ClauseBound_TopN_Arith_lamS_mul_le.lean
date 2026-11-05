-- Prove2me | solution 1 for ClauseBound.TopN.Arith.lamS_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:50:24.936331+00:00
-- url     : https://prove2.me/submissions/24ab8017-e32d-40f0-a731-f016b7bf75fd

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
theorem _root_.solution (K g Ub P : ℕ) : lamS K g Ub P * K ^ 3 ≤ K ^ 3 + K * Ub + g * P := Nat.div_mul_le_self _ _
end ClauseBound.TopN.Arith
