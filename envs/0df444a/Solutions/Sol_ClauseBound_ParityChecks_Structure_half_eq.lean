-- Prove2me | solution 1 for ClauseBound.ParityChecks.Structure.half_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:15:23.004001+00:00
-- url     : https://prove2.me/submissions/666c3a7b-bc0b-482c-a362-2bd789785f5f

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
theorem _root_.solution (q : ℕ) : (1 / 2 : ℚ) * (1 + (-1) ^ q) = (ev q : ℚ) := by
  unfold ev
  rcases Nat.even_or_odd q with h | h
  · rw [h.neg_one_pow, if_pos h]; norm_num
  · rw [h.neg_one_pow, if_neg (Nat.not_even_iff_odd.2 h)]; norm_num
end ClauseBound.ParityChecks.Structure
