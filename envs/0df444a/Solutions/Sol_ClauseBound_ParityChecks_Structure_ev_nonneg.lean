-- Prove2me | solution 1 for ClauseBound.ParityChecks.Structure.ev_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:15:24.172236+00:00
-- url     : https://prove2.me/submissions/6aa3d02f-8026-4aed-99d2-674a55333cfe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Structure

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Structure
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Structure
theorem _root_.solution (q : ℕ) : 0 ≤ ev q := by
  unfold ev
  split_ifs <;> norm_num
end ClauseBound.ParityChecks.Structure
