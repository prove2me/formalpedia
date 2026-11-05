-- Prove2me | solution 1 for ClauseBound.ParityChecks.BudgetOL.le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:45:27.970046+00:00
-- url     : https://prove2.me/submissions/9fd0f00c-35fa-4d31-9322-2d9c60e08760

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL

set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (bsum)
namespace ClauseBound.ParityChecks.BudgetOL
theorem _root_.solution (a b c d : ℕ) : a ≤ a + b + c + d ∧ b ≤ a + b + c + d ∧ c ≤ a + b + c + d ∧ d ≤ a + b + c + d := by omega
end ClauseBound.ParityChecks.BudgetOL
