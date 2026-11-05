-- Prove2me | solution 1 for ClauseBound.Alg.TopArith.cube_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:25.383405+00:00
-- url     : https://prove2.me/submissions/1faf5d91-25c3-4914-a9fd-5f6239d2dbd9

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
theorem _root_.solution (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) : K ^ 3 ≤ k * m :=
  calc K ^ 3 ≤ K ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ m := hm
    _ ≤ k * m := Nat.le_mul_of_pos_left _ hk
end ClauseBound.Alg.TopArith
