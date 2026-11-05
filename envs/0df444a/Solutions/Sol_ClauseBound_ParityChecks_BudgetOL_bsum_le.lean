-- Prove2me | solution 1 for ClauseBound.ParityChecks.BudgetOL.bsum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:29:12.243885+00:00
-- url     : https://prove2.me/submissions/8437c36b-072f-4ce7-9a6a-5cbc243c051a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_bsum_tauOf_le


set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (bsum)
namespace ClauseBound.ParityChecks.BudgetOL
theorem _root_.solution (k s : ℕ) : bsum (tauOf s) k ≤ 2 ^ betaN k s := by
  refine (bsum_tauOf_le k s).trans (Nat.pow_le_pow_right (by norm_num) ?_)
  have e : (4 * s + 17) * (2 ^ (k + 1) + 1) = (4 * s + 17) * 2 ^ (k + 1) + (4 * s + 17) := by ring
  unfold betaN
  omega
end ClauseBound.ParityChecks.BudgetOL
