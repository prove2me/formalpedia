-- Prove2me | solution 1 for ClauseBound.ParityChecks.Shape.pow_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:50.505231+00:00
-- url     : https://prove2.me/submissions/b38f9f59-8e61-414d-b1ed-815fa1ede6ed

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_ClauseBound_ParityChecks_Shape_pr_nonneg
import Theorems.Thm_ClauseBound_ParityChecks_Shape_pow_two_mul_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks
namespace ClauseBound.ParityChecks.Shape
theorem _root_.solution (nb N : ℕ) (h : 1 ≤ nb) : (1 + pr nb) ^ N ≤ 2 ^ (3 * N / (2 * nb) + 1) := by
  have hp := pr_nonneg nb
  have ht : 3 * N < 2 * nb * (3 * N / (2 * nb) + 1) := Nat.lt_mul_div_succ _ (by omega)
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega : 2 * nb ≠ 0)).1 ?_
  calc ((1 + pr nb) ^ N) ^ (2 * nb) = ((1 + pr nb) ^ (2 * nb)) ^ N := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ 8 ^ N := pow_le_pow_left₀ (by positivity) (pow_two_mul_le nb h) _
    _ = 2 ^ (3 * N) := by rw [pow_mul]; norm_num
    _ ≤ 2 ^ (2 * nb * (3 * N / (2 * nb) + 1)) := pow_le_pow_right₀ (by norm_num) ht.le
    _ = (2 ^ (3 * N / (2 * nb) + 1)) ^ (2 * nb) := by rw [← pow_mul, Nat.mul_comm]
end ClauseBound.ParityChecks.Shape
