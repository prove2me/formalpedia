-- Prove2me | solution 1 for ClauseBound.ParityChecks.Martingale.card_eq_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:01:34.280272+00:00
-- url     : https://prove2.me/submissions/b8df2b52-1a51-4f5c-b03a-e3950e429cb4

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
omit [Fintype E]
namespace ClauseBound.ParityChecks.Martingale
theorem _root_.solution {D : Finset E} {e : E} (he : e ∈ D) : #D = #(D.erase e) + 1 := by
  have h := card_erase_of_mem he
  have h0 : 0 < #D := card_pos.2 ⟨e, he⟩
  omega
end ClauseBound.ParityChecks.Martingale
