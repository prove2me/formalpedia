-- Prove2me | solution 1 for ClauseBound.ParityChecks.Approx.ev_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:37.884014+00:00
-- url     : https://prove2.me/submissions/68fb6802-3e5f-4f9d-b9b5-1a45698aea6f

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
theorem _root_.solution (q : ℕ) : 0 ≤ ev q := by
  unfold ev; split_ifs <;> norm_num
end ClauseBound.ParityChecks.Approx
