-- Prove2me | solution 1 for ClauseBound.Alg.TopArith.one_le_lam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:25:53.977704+00:00
-- url     : https://prove2.me/submissions/d5200639-f2a2-4a11-9c14-e69e5b96940a

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
theorem _root_.solution (hK : 2 ≤ K) : 1 ≤ lamTopK K (3 * K ^ 8) k m := by
  unfold lamTopK
  rw [Nat.one_le_div_iff (by positivity)]
  omega
end ClauseBound.Alg.TopArith
