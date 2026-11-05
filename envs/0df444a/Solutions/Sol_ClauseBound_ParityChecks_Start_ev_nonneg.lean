-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.ev_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:22:50.804426+00:00
-- url     : https://prove2.me/submissions/3546d94d-9d9d-4033-9008-809022a68f4b

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
theorem _root_.solution (q : ℕ) : (0 : ℚ) ≤ (ev q : ℚ) := by
  unfold ev; split_ifs <;> simp
end ClauseBound.ParityChecks.Start
