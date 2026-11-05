-- Prove2me | solution 1 for ClauseBound.ParityChecks.Structure.pr_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:12:53.549472+00:00
-- url     : https://prove2.me/submissions/c34de306-46bc-4b99-8646-771696c1f1f5

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
theorem _root_.solution {nb : ℕ} (h : 2 ≤ nb) : 0 < pr nb := by
  have : (0 : ℚ) < nb := by exact_mod_cast (by omega : 0 < nb)
  unfold pr
  positivity
end ClauseBound.ParityChecks.Structure
