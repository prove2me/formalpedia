-- Prove2me | solution 1 for ClauseBound.Alg.TopArith.two_g_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:36:54.152235+00:00
-- url     : https://prove2.me/submissions/c8cb217d-cdaa-4300-ba8e-0e7cf603f7b4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopArith

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.TopArith
open PaddedDescent.F
variable {K k m : ℕ}
namespace ClauseBound.Alg.TopArith
theorem _root_.solution (hK : 2 ≤ K) : 2 * (3 * K ^ 8) / K = 6 * K ^ 7 := by
  have : 2 * (3 * K ^ 8) = 6 * K ^ 7 * K := by ring
  rw [this, Nat.mul_div_cancel _ (by omega)]
end ClauseBound.Alg.TopArith
