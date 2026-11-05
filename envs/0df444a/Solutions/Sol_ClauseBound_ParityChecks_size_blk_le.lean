-- Prove2me | solution 1 for ClauseBound.ParityChecks.size_blk_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:38:28.735332+00:00
-- url     : https://prove2.me/submissions/ccb4f098-81a4-4e59-9881-3d94771efb0b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Params
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Theorems.Thm_ClauseBound_ParityChecks_blkOL_two_pow_le
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_RebalanceArith_size_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
namespace ClauseBound.ParityChecks
theorem _root_.solution (β n : ℕ) : Nat.size (blkOL (2 ^ β) * (7 * n + 1)) ≤ 2 * β + Nat.size n + 10 := by
  rw [Nat.size_le]
  have h1 := blkOL_two_pow_le β
  have h2 : 7 * n + 1 ≤ 2 ^ (Nat.size n + 3) := by
    have := Nat.lt_size_self n
    rw [pow_add]
    omega
  calc blkOL (2 ^ β) * (7 * n + 1) ≤ 2 ^ (2 * β + 5) * 2 ^ (Nat.size n + 3) := Nat.mul_le_mul h1 h2
    _ = 2 ^ (2 * β + Nat.size n + 8) := by rw [← pow_add]; congr 1; ring
    _ < 2 ^ (2 * β + Nat.size n + 10) := Nat.pow_lt_pow_right (by norm_num) (by omega)
end ClauseBound.ParityChecks
