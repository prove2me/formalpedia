-- Prove2me | solution 1 for ClauseBound.ParityChecks.Approx.ev_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:59.14434+00:00
-- url     : https://prove2.me/submissions/91e3b6c3-92ab-4b56-bad8-55e395943f43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic
import Definitions.Def_ClauseBound_ParityChecks_Approx

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Approx
open Finset _root_.ParityChecks
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Approx
theorem _root_.solution (q : ℕ) : ev q ≤ 1 := by
  unfold ev; split_ifs <;> norm_num
end ClauseBound.ParityChecks.Approx
