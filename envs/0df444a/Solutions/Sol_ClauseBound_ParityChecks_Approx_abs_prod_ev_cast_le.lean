-- Prove2me | solution 1 for ClauseBound.ParityChecks.Approx.abs_prod_ev_cast_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:03:18.634768+00:00
-- url     : https://prove2.me/submissions/f946997b-8aec-4e32-be92-85ed82a41046

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Theorems.Thm_ClauseBound_ParityChecks_Approx_abs_prod_ev_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Approx
open Finset _root_.ParityChecks
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Approx
theorem _root_.solution (s : Finset ℕ) (q : ℕ → ℕ) : |∏ i ∈ s, (ev (q i) : ℚ)| ≤ 1 := by
  have h := abs_prod_ev_le s q
  have h2 : ((|∏ i ∈ s, ev (q i)| : ℤ) : ℚ) ≤ ((1 : ℤ) : ℚ) := Int.cast_le.2 h
  simpa using h2
end ClauseBound.ParityChecks.Approx
