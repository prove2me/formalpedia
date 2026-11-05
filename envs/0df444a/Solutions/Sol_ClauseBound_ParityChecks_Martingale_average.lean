-- Prove2me | solution 1 for ClauseBound.ParityChecks.Martingale.average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:22:12.987121+00:00
-- url     : https://prove2.me/submissions/ff4b07ab-47a3-45b6-89d6-1adfbafa1df0

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
namespace ClauseBound.ParityChecks.Martingale
theorem _root_.solution (p x : ℚ) (k : ℕ) (hp : 1 + p ≠ 0) : p * (2 * x / (1 + p) ^ (k + 1)) + (1 - p) * (x / (1 + p) ^ (k + 1)) = x / (1 + p) ^ k := by
  field_simp
  ring
end ClauseBound.ParityChecks.Martingale
