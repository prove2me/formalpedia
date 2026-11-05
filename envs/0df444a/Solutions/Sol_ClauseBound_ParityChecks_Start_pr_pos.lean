-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.pr_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:22:49.618772+00:00
-- url     : https://prove2.me/submissions/87fc9f46-53b0-4378-b2de-c3d57865c765

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
theorem _root_.solution {nb : ℕ} (h : 2 ≤ nb) : 0 < pr nb := by
  have : (0 : ℚ) < nb := by exact_mod_cast (by omega : 0 < nb)
  unfold pr; positivity
end ClauseBound.ParityChecks.Start
