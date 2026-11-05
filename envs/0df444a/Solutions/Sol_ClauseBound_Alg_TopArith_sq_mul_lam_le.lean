-- Prove2me | solution 1 for ClauseBound.Alg.TopArith.sq_mul_lam_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:21:04.241414+00:00
-- url     : https://prove2.me/submissions/4af27734-5aa2-4490-a853-d8baf3fe2cc3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopArith
import Theorems.Thm_ClauseBound_Alg_TopArith_g_mul_P_le
import Theorems.Thm_ClauseBound_Alg_TopArith_cube_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.TopArith
open PaddedDescent.F
variable {K k m : ℕ}
namespace ClauseBound.Alg.TopArith
theorem _root_.solution (hK : 2 ≤ K) (hk : 1 ≤ k) (hm : K ^ 9 ≤ m) : K ^ 2 * lamTopK K (3 * K ^ 8) k m ≤ 8 * (k * m) := by
  have h := g_mul_P_le hK hk hm
  have h3 := cube_le hK hk hm
  have hd : lamTopK K (3 * K ^ 8) k m * K ^ 3 ≤ K ^ 3 + K * (2 * k * m) + 3 * K ^ 8 * PtopK (3 * K ^ 8) k m := Nat.div_mul_le_self _ _
  have hK0 : 0 < K := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hK0
  have h5 : 5 * (k * m) ≤ 5 * (k * m) * K := Nat.le_mul_of_pos_right _ hK0
  have h6 : K ^ 3 ≤ k * m * K := h3.trans (Nat.le_mul_of_pos_right _ hK0)
  calc K ^ 2 * lamTopK K (3 * K ^ 8) k m * K = lamTopK K (3 * K ^ 8) k m * K ^ 3 := by ring
    _ ≤ K ^ 3 + K * (2 * k * m) + 3 * K ^ 8 * PtopK (3 * K ^ 8) k m := hd
    _ ≤ k * m * K + K * (2 * k * m) + 5 * (k * m) * K := by omega
    _ = 8 * (k * m) * K := by ring
end ClauseBound.Alg.TopArith
