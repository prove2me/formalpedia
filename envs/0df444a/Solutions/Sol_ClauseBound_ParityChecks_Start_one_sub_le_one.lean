-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.one_sub_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:10:18.943961+00:00
-- url     : https://prove2.me/submissions/888c68ab-55d3-4ef0-865d-34e707da1ab4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start
import Theorems.Thm_ClauseBound_ParityChecks_Start_pr_pos

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset
namespace ClauseBound.ParityChecks.Start
theorem _root_.solution {nb : ℕ} (h : 2 ≤ nb) : 1 - 2 * pr nb ≤ 1 := by
  have := pr_pos h
  linarith
end ClauseBound.ParityChecks.Start
