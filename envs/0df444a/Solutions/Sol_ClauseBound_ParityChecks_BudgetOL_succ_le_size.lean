-- Prove2me | solution 1 for ClauseBound.ParityChecks.BudgetOL.succ_le_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:46:03.41681+00:00
-- url     : https://prove2.me/submissions/bd4507ca-deef-471b-8d2c-02bf5184b92d

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
theorem _root_.solution (n : ℕ) : n + 1 ≤ 2 ^ Nat.size n := Nat.lt_size_self n
end ClauseBound.ParityChecks.BudgetOL
