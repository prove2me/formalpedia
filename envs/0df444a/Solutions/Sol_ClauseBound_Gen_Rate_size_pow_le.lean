-- Prove2me | solution 1 for ClauseBound.Gen.Rate.size_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:43:27.191816+00:00
-- url     : https://prove2.me/submissions/5b495bed-a4c3-4f27-9322-0556e449feb9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_RateAux
import Theorems.Thm_Groundwork_RebalanceArith_size_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Nat (size)
namespace ClauseBound.Gen.Rate
theorem _root_.solution (a n : ℕ) : size (a ^ n) ≤ n * size a + 1 := by
  rw [Nat.size_le]
  calc a ^ n ≤ (2 ^ size a) ^ n := Nat.pow_le_pow_left (Nat.lt_size_self a).le n
    _ = 2 ^ (n * size a) := by rw [← pow_mul, mul_comm]
    _ < 2 ^ (n * size a + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
end ClauseBound.Gen.Rate
