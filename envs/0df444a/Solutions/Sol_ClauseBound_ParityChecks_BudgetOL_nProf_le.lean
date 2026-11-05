-- Prove2me | solution 1 for ClauseBound.ParityChecks.BudgetOL.nProf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:43:51.016955+00:00
-- url     : https://prove2.me/submissions/c9da1805-8062-447c-9668-85c69307a9d3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_succ_le_size

set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (bsum)
namespace ClauseBound.ParityChecks.BudgetOL
theorem _root_.solution (g M : ℕ) : Mark.nProf g M 3 ≤ 2 ^ (g * g * 3 * Nat.size M) := by
  unfold Mark.nProf
  calc (M + 1) ^ (g * g * 3) ≤ (2 ^ Nat.size M) ^ (g * g * 3) := Nat.pow_le_pow_left (succ_le_size M) _
    _ = 2 ^ (g * g * 3 * Nat.size M) := by rw [← pow_mul, Nat.mul_comm (Nat.size M)]
end ClauseBound.ParityChecks.BudgetOL
