-- Prove2me | solution 1 for ClauseBound.ParityChecks.BudgetOL.stBudgetO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:48:01.834781+00:00
-- url     : https://prove2.me/submissions/2303e81b-154f-483b-af72-137dbca945c9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_nProf_le
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_checks_le
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_stack_le
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_le_four
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_Arith_sum_choose_le_two_pow


set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (bsum)
namespace ClauseBound.ParityChecks.BudgetOL
theorem _root_.solution : StBudgetO := by
  intro k K n s F hk hs hF
  have up : ∀ {x t : ℕ}, x ≤ 2 ^ t → t ≤ restO k K n s → x ≤ F := fun h1 h2 => h1.trans ((Nat.pow_le_pow_right (by norm_num) h2).trans hF)
  refine ⟨up (nProf_le _ _) (le_four _ _ _ _).1, up (checks_le _ _) (le_four _ _ _ _).2.1, ?_, up (stack_le hk n s) (le_four _ _ _ _).2.2.2⟩
  have h1 := Arith.sum_choose_le_two_pow hs n
  have h2 : 2 ^ (n / 2 ^ s + 1 + 1) ≤ F := up le_rfl (le_four _ _ _ _).2.2.1
  rw [pow_succ] at h2
  omega
end ClauseBound.ParityChecks.BudgetOL
