-- Prove2me | solution 1 for ClauseBound.ParityChecks.BudgetOL.inLen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:43:54.442262+00:00
-- url     : https://prove2.me/submissions/0ea71d82-3fdf-4eef-8a5e-564bf3348b27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_mul_le_pow
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_succ_le_size
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (bsum)
namespace ClauseBound.ParityChecks.BudgetOL
theorem _root_.solution (k n : ℕ) : inLen k n ≤ 2 ^ (3 * k + 1 + (k + 1) * Nat.size n) := by
  have h1 := succ_le_size n
  have h2 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have h3 : k * 2 ^ k + 1 ≤ 2 ^ (k + k) := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    calc k * 2 ^ k + 1 ≤ (k + 1) * 2 ^ k := by nlinarith
      _ ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (k + k) := (pow_add _ _ _).symm
  have h4 : n + 2 ≤ 2 ^ (Nat.size n + 1) := by rw [pow_succ]; omega
  have h5 : (n + 2) ^ (k + 1) ≤ 2 ^ ((Nat.size n + 1) * (k + 1)) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left h4 _
  unfold inLen
  refine (mul_le_pow h3 h5).trans (Nat.pow_le_pow_right (by norm_num) (le_of_eq ?_))
  ring
end ClauseBound.ParityChecks.BudgetOL
