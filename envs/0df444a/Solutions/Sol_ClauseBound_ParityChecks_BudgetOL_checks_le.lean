-- Prove2me | solution 1 for ClauseBound.ParityChecks.BudgetOL.checks_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:29:36.664065+00:00
-- url     : https://prove2.me/submissions/39246ec0-3925-4732-83f3-db9475bd7248

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_mul_le_pow
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_add_le_pow
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_succ_le_size

set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (bsum)
namespace ClauseBound.ParityChecks.BudgetOL
theorem _root_.solution (n m : ℕ) : 8 * (6 * n + 1) * (m + 1) * (Nat.size m + 2) + 8 ≤ 2 ^ (3 * Nat.size m + 3 * Nat.size n + 12) := by
  obtain ⟨a, ha⟩ : ∃ a, a = Nat.size m := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = Nat.size n := ⟨_, rfl⟩
  rw [← ha, ← hz]
  have h1 : m + 1 ≤ 2 ^ a := ha ▸ succ_le_size m
  have h2 : n + 1 ≤ 2 ^ z := hz ▸ succ_le_size n
  have h3 : 8 * (6 * n + 1) ≤ 2 ^ (z + 6) := by rw [pow_add]; omega
  have h4 : a + 2 ≤ 2 ^ (a + 1) := by
    have : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
    rw [pow_succ]
    omega
  have h5 : 8 * (6 * n + 1) * (m + 1) * (a + 2) ≤ 2 ^ (z + 6 + a + (a + 1)) := mul_le_pow (mul_le_pow h3 h1) h4
  exact add_le_pow h5 (by norm_num : 8 ≤ 2 ^ 3) (by omega) (by omega)
end ClauseBound.ParityChecks.BudgetOL
