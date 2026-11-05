-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.one_sub_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:10:10.929725+00:00
-- url     : https://prove2.me/submissions/b2a3bef3-0185-4ceb-9019-a08e7f8b81de

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset
namespace ClauseBound.ParityChecks.Start
theorem _root_.solution {nb : ℕ} (h : 2 ≤ nb) : 0 ≤ 1 - 2 * pr nb := by
  have h2 : (2 : ℚ) ≤ nb := by exact_mod_cast h
  have : pr nb ≤ 1 / 2 := by unfold pr; exact one_div_le_one_div_of_le (by norm_num) h2
  linarith
end ClauseBound.ParityChecks.Start
