-- Prove2me | solution 1 for ClauseBound.Alg.TopArith.P_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:25:44.974283+00:00
-- url     : https://prove2.me/submissions/01c5c9ce-d08d-4602-b861-bb6250792e02

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopArith
import Theorems.Thm_ClauseBound_Alg_TopArith_g_mul_P_le
import Theorems.Thm_ClauseBound_Alg_TopArith_two_g_div

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.TopArith
open PaddedDescent.F
variable {K k m : ℕ}
namespace ClauseBound.Alg.TopArith
theorem _root_.solution (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) :
    PtopK (3 * K ^ 8) k m * (2 * (3 * K ^ 8) / K + 1) * K ≤ 15 * (k * m) := by
  have h := g_mul_P_le hK hk hm
  rw [two_g_div hK]
  have h1 : (6 * K ^ 7 + 1) * K ≤ 3 * (3 * K ^ 8) := by
    have : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) _
    calc (6 * K ^ 7 + 1) * K = 6 * K ^ 8 + K := by ring
      _ ≤ 3 * (3 * K ^ 8) := by omega
  calc PtopK (3 * K ^ 8) k m * (6 * K ^ 7 + 1) * K = PtopK (3 * K ^ 8) k m * ((6 * K ^ 7 + 1) * K) := by ring
    _ ≤ PtopK (3 * K ^ 8) k m * (3 * (3 * K ^ 8)) := Nat.mul_le_mul_left _ h1
    _ = 3 * (3 * K ^ 8 * PtopK (3 * K ^ 8) k m) := by ring
    _ ≤ 15 * (k * m) := by omega
end ClauseBound.Alg.TopArith
