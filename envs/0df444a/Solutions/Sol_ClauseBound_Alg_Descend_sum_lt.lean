-- Prove2me | solution 1 for ClauseBound.Alg.Descend.sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:44:40.752398+00:00
-- url     : https://prove2.me/submissions/10b496de-680f-43c8-b6b4-c506a11e8675

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_Descend
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Descend
import Theorems.Thm_ClauseBound_Alg_Descend_two_pow_size_le
import Theorems.Thm_ClauseBound_Alg_Descend_factor_lt
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Descend
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists
namespace ClauseBound.Alg.Descend
theorem _root_.solution {a b : ℤ} {D z r cnt n E : ℕ} (ha : a.natAbs < 2 ^ z) (hD : D ≤ 2 ^ r) (hn : 1 ≤ n)
    (hb : b.natAbs ≤ cnt * 2 ^ (Nat.size n + E)) : (a * (D : ℕ) + b).natAbs < 2 ^ (z + r + Nat.size (cnt * n) + E + 2) := by
  have h1 : (a * (D : ℕ)).natAbs < 2 ^ (z + r + (Nat.size (cnt * n) + E + 1)) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact factor_lt ha hD
  have h2 : b.natAbs < 2 ^ (z + r + (Nat.size (cnt * n) + E + 1)) := by
    calc b.natAbs ≤ cnt * (2 ^ Nat.size n * 2 ^ E) := by rw [← pow_add]; exact hb
      _ ≤ cnt * (2 * n * 2 ^ E) := by gcongr; exact two_pow_size_le hn
      _ = cnt * n * (2 * 2 ^ E) := by ring
      _ < 2 ^ Nat.size (cnt * n) * (2 * 2 ^ E) := Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by positivity)
      _ = 2 ^ (Nat.size (cnt * n) + E + 1) := by ring
      _ ≤ 2 ^ (z + r + (Nat.size (cnt * n) + E + 1)) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
  have h3 := Int.natAbs_add_le (a * (D : ℕ)) b
  have h4 : 2 ^ (z + r + Nat.size (cnt * n) + E + 2) = 2 * 2 ^ (z + r + (Nat.size (cnt * n) + E + 1)) := by
    rw [← pow_succ']; congr 1; omega
  omega
end ClauseBound.Alg.Descend
