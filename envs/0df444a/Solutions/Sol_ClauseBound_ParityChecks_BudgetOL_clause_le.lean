-- Prove2me | solution 1 for ClauseBound.ParityChecks.BudgetOL.clause_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:43:28.911411+00:00
-- url     : https://prove2.me/submissions/aa3f9c50-3fad-4622-b131-3c379b931aa9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_succ_le_size
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (bsum)
namespace ClauseBound.ParityChecks.BudgetOL
theorem _root_.solution (k n : ℕ) : k * (3 * n + 5) + 10 ≤ 2 ^ (k + Nat.size n + 4) := by
  have h1 := succ_le_size n
  have h2 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have h3 : (k + 1) * (n + 1) ≤ 2 ^ k * 2 ^ Nat.size n := Nat.mul_le_mul h2 h1
  have h4 : k * (3 * n + 5) + 10 ≤ 16 * ((k + 1) * (n + 1)) := by nlinarith
  calc k * (3 * n + 5) + 10 ≤ 16 * (2 ^ k * 2 ^ Nat.size n) := h4.trans (Nat.mul_le_mul_left _ h3)
    _ = 2 ^ (k + Nat.size n + 4) := by rw [pow_add, pow_add]; ring
end ClauseBound.ParityChecks.BudgetOL
