-- Prove2me | solution 1 for ClauseBound.TopN.Arith.one_le_lamS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:26:53.738917+00:00
-- url     : https://prove2.me/submissions/91d6956d-ba07-492d-947b-ecdc55081f2b

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
theorem _root_.solution (hK : 1 ≤ K) (g Ub P : ℕ) : 1 ≤ lamS K g Ub P := by
  unfold lamS
  rw [Nat.le_div_iff_mul_le (by positivity)]
  omega
end ClauseBound.TopN.Arith
