-- Prove2me | solution 1 for ClauseBound.ParityChecks.Martingale.undRow_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:22:33.965421+00:00
-- url     : https://prove2.me/submissions/af04163c-db7a-415a-8a32-9fa1c7fa88da

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_Martingale

set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Martingale
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [DecidableEq E]
namespace ClauseBound.ParityChecks.Martingale
theorem _root_.solution {j j' : ℕ} (h : j' ≠ j) (D D' : Finset E) : undRow j D j' = undRow j D' j' := by simp [undRow, h]
end ClauseBound.ParityChecks.Martingale
